/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage1E03.Shapes

/-!
The source Euclidean guard schedule and its operational report contract.
-/

@[expose] public section

namespace V7
namespace Stage1E03

/-- Classical proposition decisions used locally by the Euclidean correctness proof. -/
noncomputable local instance correctnessPropDecidable (q : Prop) : Decidable q :=
  Classical.propDecidable q

/-- The accelerated endpoint passed from the estimate phase to OGM-G. -/
noncomputable def sourceU (inst : PositiveInstance 2 d x0) (M : ℝ)
    (n : ℕ) : Point d :=
  (sourceEstimateState inst.oracle M x0 n).accelerated

/-- The new OGM-G observations after its reused initial query. -/
noncomputable def sourceNewTrace (inst : PositiveInstance 2 d x0)
    (M : ℝ) (n : ℕ) : List (Observation d) :=
  let cfg := O3.stage9ExecutionConfig n inst.oracle M (sourceU inst M n)
  (List.range n).map fun j =>
    inst.oracle.observe (O3.ogmgState cfg (j + 1)).current

/-- All pairwise interpolation checks for the OGM-G observations. -/
noncomputable def sourceInterpolationSchedule
    (inst : PositiveInstance 2 d x0) (M : ℝ) (n : ℕ) :
    List (ObservableGuardCheck d) :=
  let cfg := O3.stage9ExecutionConfig n inst.oracle M (sourceU inst M n)
  allInterpolationChecks n fun i =>
    inst.oracle.observe (O3.ogmgState cfg i).current

/-- The oracle observation at the terminal OGM-G gradient-step point. -/
noncomputable def sourceTerminalObservation
    (inst : PositiveInstance 2 d x0) (M : ℝ) (n : ℕ) : Observation d :=
  let cfg := O3.stage9ExecutionConfig n inst.oracle M (sourceU inst M n)
  inst.oracle.observe (O3.ogmgV cfg n)

/-- The descent check between the final OGM-G query and its gradient step. -/
noncomputable def sourceTerminalGuard
    (inst : PositiveInstance 2 d x0) (M : ℝ) (n : ℕ) :
    ObservableGuardCheck d :=
  let cfg := O3.stage9ExecutionConfig n inst.oracle M (sourceU inst M n)
  terminalCheck (inst.oracle.observe (O3.ogmgState cfg n).current)
    (inst.oracle.observe (O3.ogmgV cfg n))

/-- The complete planned trace of both Euclidean phases and the terminal query. -/
noncomputable def sourcePlannedTrace (inst : PositiveInstance 2 d x0)
    (M : ℝ) (n : ℕ) : List (Observation d) :=
  phaseATraceFrom inst M 0 n ++ sourceNewTrace inst M n ++
    [sourceTerminalObservation inst M n]

/-- The complete planned guard schedule of the Euclidean trial. -/
noncomputable def sourceGuardSchedule (inst : PositiveInstance 2 d x0)
    (M : ℝ) (n : ℕ) : List (ObservableGuardCheck d) :=
  phaseAGuardsFrom inst M 0 n ++ sourceInterpolationSchedule inst M n ++
    [sourceTerminalGuard inst M n]

theorem source_u_mem_preterminal (inst : PositiveInstance 2 d x0)
    (M : ℝ) (n i : ℕ) (hn : 1 ≤ n) (hi : i ≤ n) :
    inst.oracle.observe
      (O3.ogmgState (O3.stage9ExecutionConfig n inst.oracle M
        (sourceU inst M n)) i).current ∈
      phaseATraceFrom inst M 0 n ++ sourceNewTrace inst M n := by
  by_cases hi0 : i = 0
  · subst i
    apply List.mem_append_left
    simp only [phaseATraceFrom, List.mem_flatMap]
    refine ⟨n - 1, List.mem_range.mpr (by omega), ?_⟩
    right
    have hnsub : n - 1 + 1 = n := by omega
    have hs := sourceEstimateState_succ inst.oracle M x0 (n - 1)
    rw [hnsub] at hs
    apply List.mem_singleton.mpr
    simpa [sourceU, O3.stage9ExecutionConfig] using
      congrArg inst.oracle.observe
        (congrArg O3.EuclideanEstimateState.accelerated hs)
  · apply List.mem_append_right
    simp only [sourceNewTrace, List.mem_map]
    refine ⟨i - 1, List.mem_range.mpr (by omega), ?_⟩
    congr 3
    omega

theorem source_preterminal_pairs (inst : PositiveInstance 2 d x0)
    (M : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∀ check ∈ phaseAGuardsFrom inst M 0 n ++
        sourceInterpolationSchedule inst M n,
      check.xPair ∈ phaseATraceFrom inst M 0 n ++ sourceNewTrace inst M n ∧
      check.yPair ∈ phaseATraceFrom inst M 0 n ++ sourceNewTrace inst M n := by
  intro check hcheck
  rcases List.mem_append.mp hcheck with hA | hI
  · simp only [phaseAGuardsFrom, List.mem_map] at hA
    rcases hA with ⟨k, hk, rfl⟩
    constructor <;> apply List.mem_append_left
    · simp only [phaseATraceFrom, List.mem_flatMap]
      exact ⟨k, hk, by simp [upperCheck]⟩
    · simp only [phaseATraceFrom, List.mem_flatMap]
      exact ⟨k, hk, by simp [upperCheck]⟩
  · simp only [sourceInterpolationSchedule, allInterpolationChecks,
      List.mem_flatMap, List.mem_map] at hI
    rcases hI with ⟨i, hi, j, hj, rfl⟩
    exact ⟨by simpa [interpolationCheck] using
        source_u_mem_preterminal inst M n i hn (by
          exact Nat.le_of_lt_succ (List.mem_range.mp hi)),
      by simpa [interpolationCheck] using
        source_u_mem_preterminal inst M n j hn (by
          exact Nat.le_of_lt_succ (List.mem_range.mp hj))⟩

theorem source_schedule_pairs (inst : PositiveInstance 2 d x0)
    (M : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∀ check ∈ sourceGuardSchedule inst M n,
      check.xPair ∈ sourcePlannedTrace inst M n ∧
      check.yPair ∈ sourcePlannedTrace inst M n := by
  intro check hcheck
  simp only [sourceGuardSchedule, List.mem_append, List.mem_singleton] at hcheck
  rcases hcheck with hpre | hterminal
  · have hp := source_preterminal_pairs inst M n hn check
      (List.mem_append.mpr hpre)
    exact ⟨List.mem_append_left _ hp.1, List.mem_append_left _ hp.2⟩
  · subst check
    constructor
    · apply List.mem_append_left
      simpa [sourceTerminalGuard, terminalCheck, sourceU] using
        source_u_mem_preterminal inst M n n hn (le_refl n)
    · simp [sourceTerminalGuard, sourceTerminalObservation,
        sourcePlannedTrace, terminalCheck]

/-- The possible early-failure and completed-report shapes of the Euclidean trial. -/
def FullReportShape (inst : PositiveInstance 2 d x0) (eps M : ℝ)
    (n : ℕ) (report : TrialReport d) : Prop :=
  (∃ r < n, ∃ failed,
    FailureLedger 2 M report failed ∧ GuardPairsInTrace report ∧
    failed.kind = .upperModel ∧
    report.trace <+: sourcePlannedTrace inst M n ∧
    report.checkedGuards <+: sourceGuardSchedule inst M n ∧
    report.trace.length = 2 * (r + 1) ∧
    report.checkedGuards.length = r + 1) ∨
  (∃ failed, FailureLedger 2 M report failed ∧ GuardPairsInTrace report ∧
    failed.kind = .interpolation ∧
    report.trace = phaseATraceFrom inst M 0 n ++ sourceNewTrace inst M n ∧
    report.checkedGuards <+: sourceGuardSchedule inst M n) ∨
  (∃ failed, FailureLedger 2 M report failed ∧ GuardPairsInTrace report ∧
    failed.kind = .terminalDescent ∧
    report.trace = sourcePlannedTrace inst M n ∧
    report.checkedGuards = sourceGuardSchedule inst M n) ∨
  (∃ terminal, report.outcome = .success terminal ∧
    terminal = inst.oracle.observe
      (O3.ogmgState (O3.stage9ExecutionConfig n inst.oracle M
        (sourceU inst M n)) n).current ∧
    report.trace = sourcePlannedTrace inst M n ∧
    report.checkedGuards = sourceGuardSchedule inst M n ∧ GuardPairsInTrace report ∧
    (∀ check ∈ report.checkedGuards, CheckHolds 2 M check) ∧
    lpNorm 2 terminal.gradient ≤ eps) ∨
  ∃ terminal, report.outcome = .radius terminal ∧
    terminal = inst.oracle.observe
      (O3.ogmgState (O3.stage9ExecutionConfig n inst.oracle M
        (sourceU inst M n)) n).current ∧
    report.trace = sourcePlannedTrace inst M n ∧
    report.checkedGuards = sourceGuardSchedule inst M n ∧ GuardPairsInTrace report ∧
    (∀ check ∈ report.checkedGuards, CheckHolds 2 M check) ∧
    eps < lpNorm 2 terminal.gradient

theorem sourceFullReport_shape (inst : PositiveInstance 2 d x0)
    (eps M : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    FullReportShape inst eps M n (sourcePhaseAReport inst eps M n 0 n) := by
  have hA := sourcePhaseAReport_shape inst eps M n n 0 (by simp)
  rcases hA with hfail | hpass
  · left
    rcases hfail with ⟨r, hr, failed, hledger, hpairs, htp, hgp, htlen,
      hglen, hkind⟩
    refine ⟨r, hr, failed, hledger, hpairs, hkind, ?_, ?_, htlen, hglen⟩
    · apply htp.trans
      unfold sourcePlannedTrace
      refine ⟨sourceNewTrace inst M n ++
        [sourceTerminalObservation inst M n], ?_⟩
      simp [List.append_assoc]
    · apply hgp.trans
      unfold sourceGuardSchedule
      refine ⟨sourceInterpolationSchedule inst M n ++
        [sourceTerminalGuard inst M n], ?_⟩
      simp [List.append_assoc]
  · rcases hpass with ⟨hallA, hreport⟩
    rw [hreport]
    have hB := sourcePhaseBReport_shape inst eps M n (sourceU inst M n)
    dsimp only [sourceU] at hB
    rcases hB with hscale | hsuccess | hradius
    · rcases hscale with ⟨failed, hledger, hinterp | hterminal⟩
      · right; left
        rcases hinterp with ⟨hkind, htrace, hguards⟩
        refine ⟨failed, prepend_failureLedger 2 M _ _ _ failed hallA hledger,
          ?_, hkind, ?_, ?_⟩
        · intro check hmem
          have hsched : check ∈ phaseAGuardsFrom inst M 0 n ++
              sourceInterpolationSchedule inst M n := by
            simp only [prependReport, List.mem_append] at hmem
            rcases hmem with hA | hB
            · exact List.mem_append_left _ hA
            · exact List.mem_append_right _ (hguards.subset hB)
          have hp := source_preterminal_pairs inst M n hn check hsched
          simpa [prependReport, htrace, sourceNewTrace, sourceU,
            List.append_assoc] using hp
        · simp [prependReport, sourceNewTrace, sourceU,
            htrace]
        · rcases hguards with ⟨rest, hrest⟩
          refine ⟨rest ++ [sourceTerminalGuard inst M n], ?_⟩
          simp only [prependReport, sourceGuardSchedule]
          simp only [List.append_assoc]
          congr 1
          rw [← List.append_assoc]
          rw [hrest]
          simp [sourceInterpolationSchedule, sourceU]
      · right; right; left
        rcases hterminal with ⟨hkind, htrace, hguards⟩
        refine ⟨failed, prepend_failureLedger 2 M _ _ _ failed hallA hledger,
          ?_, hkind, ?_, ?_⟩
        · intro check hmem
          have hsched : check ∈ sourceGuardSchedule inst M n := by
            simp only [prependReport, List.mem_append] at hmem
            rcases hmem with hA | hB
            · apply List.mem_append_left
              exact List.mem_append_left _ hA
            · simp only [hguards, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
                sourceGuardSchedule, sourceInterpolationSchedule, sourceU, sourceTerminalGuard,
                List.append_assoc] at hB ⊢
              exact Or.inr hB
          have hp := source_schedule_pairs inst M n hn check hsched
          simpa [prependReport, sourcePlannedTrace, sourceNewTrace,
            sourceTerminalObservation, sourceU, htrace,
            List.append_assoc] using hp
        · simp [prependReport, sourcePlannedTrace, sourceNewTrace,
            sourceTerminalObservation, sourceU, htrace, List.append_assoc]
        · simp [prependReport, sourceGuardSchedule, sourceInterpolationSchedule,
            sourceTerminalGuard, sourceU, hguards, List.append_assoc]
    · right; right; right; left
      rcases hsuccess with ⟨terminal, hout, hterminal, htrace, hguards,
        hallB, hnorm⟩
      refine ⟨terminal, hout, hterminal, ?_, ?_, ?_, ?_, hnorm⟩
      · simp [prependReport, sourcePlannedTrace, sourceNewTrace,
          sourceTerminalObservation, sourceU, htrace, List.append_assoc]
      · simp [prependReport, sourceGuardSchedule, sourceInterpolationSchedule,
          sourceTerminalGuard, sourceU, hguards, List.append_assoc]
      · intro check hmem
        have hp := source_schedule_pairs inst M n hn check (by
          simpa [prependReport, sourceGuardSchedule, sourceInterpolationSchedule,
            sourceTerminalGuard, sourceU, hguards, List.append_assoc] using hmem)
        simpa [prependReport, sourcePlannedTrace, sourceNewTrace,
          sourceTerminalObservation, sourceU, htrace,
          List.append_assoc] using hp
      · intro check hmem
        simp only [prependReport, List.mem_append] at hmem
        rcases hmem with hmem | hmem
        · exact hallA check hmem
        · exact hallB check hmem
    · right; right; right; right
      rcases hradius with ⟨terminal, hout, hterminal, htrace, hguards,
        hallB, hnorm⟩
      refine ⟨terminal, hout, hterminal, ?_, ?_, ?_, ?_, hnorm⟩
      · simp [prependReport, sourcePlannedTrace, sourceNewTrace,
          sourceTerminalObservation, sourceU, htrace, List.append_assoc]
      · simp [prependReport, sourceGuardSchedule, sourceInterpolationSchedule,
          sourceTerminalGuard, sourceU, hguards, List.append_assoc]
      · intro check hmem
        have hp := source_schedule_pairs inst M n hn check (by
          simpa [prependReport, sourceGuardSchedule, sourceInterpolationSchedule,
            sourceTerminalGuard, sourceU, hguards, List.append_assoc] using hmem)
        simpa [prependReport, sourcePlannedTrace, sourceNewTrace,
          sourceTerminalObservation, sourceU, htrace,
          List.append_assoc] using hp
      · intro check hmem
        simp only [prependReport, List.mem_append] at hmem
        rcases hmem with hmem | hmem
        · exact hallA check hmem
        · exact hallB check hmem

theorem source_lists_eq_carriers (inst : PositiveInstance 2 d x0)
    (M D : ℝ) (n : ℕ) :
    let phaseA := sourcePhaseAData inst M D n
    let phaseB := sourcePhaseBData inst M n (sourceU inst M n)
    sourcePlannedTrace inst M n = euclideanPlannedTrace inst phaseA phaseB ∧
    sourceGuardSchedule inst M n = euclideanGuardSchedule inst phaseA phaseB := by
  dsimp only
  constructor
  · unfold sourcePlannedTrace sourceNewTrace sourceTerminalObservation
    unfold phaseATraceFrom euclideanPlannedTrace sourcePhaseAData
    unfold sourcePhaseBData sourceU
    simp only [Nat.zero_add]
  · unfold sourceGuardSchedule sourceInterpolationSchedule sourceTerminalGuard
    unfold phaseAGuardsFrom euclideanGuardSchedule sourcePhaseAData
    unfold sourcePhaseBData sourceU allInterpolationChecks
    simp only [Nat.zero_add, exactGuardCheck, upperCheck, interpolationCheck,
      terminalCheck]

@[simp] theorem sourceNewTrace_length (inst : PositiveInstance 2 d x0)
    (M : ℝ) (n : ℕ) : (sourceNewTrace inst M n).length = n := by
  simp [sourceNewTrace]

@[simp] theorem sourcePlannedTrace_length (inst : PositiveInstance 2 d x0)
    (M : ℝ) (n : ℕ) :
    (sourcePlannedTrace inst M n).length = 2 * n + n + 1 := by
  simp [sourcePlannedTrace]
  omega

theorem fullShape_prefixes {inst : PositiveInstance 2 d x0}
    {eps M : ℝ} {n : ℕ} {report : TrialReport d}
    (hshape : FullReportShape inst eps M n report) :
    report.trace <+: sourcePlannedTrace inst M n ∧
    report.checkedGuards <+: sourceGuardSchedule inst M n := by
  rcases hshape with hA | hI | hT | hS | hR
  · rcases hA with ⟨r, hr, failed, hledger, hpairs, hkind, ht, hg, htl, hgl⟩
    exact ⟨ht, hg⟩
  · rcases hI with ⟨failed, hledger, hpairs, hkind, htrace, hguards⟩
    constructor
    · rw [htrace]
      unfold sourcePlannedTrace
      exact List.prefix_append _ _
    · exact hguards
  · rcases hT with ⟨failed, hledger, hpairs, hkind, htrace, hguards⟩
    exact ⟨htrace ▸ List.prefix_refl _, hguards ▸ List.prefix_refl _⟩
  · rcases hS with ⟨terminal, hout, hterminal, htrace, hguards, hpairs, hall, hn⟩
    exact ⟨htrace ▸ List.prefix_refl _, hguards ▸ List.prefix_refl _⟩
  · rcases hR with ⟨terminal, hout, hterminal, htrace, hguards, hpairs, hall, hn⟩
    exact ⟨htrace ▸ List.prefix_refl _, hguards ▸ List.prefix_refl _⟩

theorem fullShape_calls_le {inst : PositiveInstance 2 d x0}
    {eps M : ℝ} {n : ℕ} {report : TrialReport d}
    (hshape : FullReportShape inst eps M n report) :
    report.calls ≤ 2 * n + n + 1 := by
  have hp := (fullShape_prefixes hshape).1.length_le
  simpa [TrialReport.calls] using hp

theorem fullShape_pairs {inst : PositiveInstance 2 d x0}
    {eps M : ℝ} {n : ℕ} {report : TrialReport d}
    (hshape : FullReportShape inst eps M n report) :
    GuardPairsInTrace report := by
  rcases hshape with hA | hI | hT | hS | hR
  · rcases hA with ⟨r, hr, failed, hledger, hpairs, rest⟩
    exact hpairs
  · rcases hI with ⟨failed, hledger, hpairs, rest⟩
    exact hpairs
  · rcases hT with ⟨failed, hledger, hpairs, rest⟩
    exact hpairs
  · rcases hS with ⟨terminal, hout, hterminal, htrace, hguards, hpairs, rest⟩
    exact hpairs
  · rcases hR with ⟨terminal, hout, hterminal, htrace, hguards, hpairs, rest⟩
    exact hpairs

theorem sourceSchedule_kinds (inst : PositiveInstance 2 d x0)
    (M : ℝ) (n : ℕ) :
    ∀ check ∈ sourceGuardSchedule inst M n,
      check.kind ∈ [.upperModel, .interpolation, .terminalDescent] := by
  intro check hmem
  simp only [sourceGuardSchedule, List.mem_append, List.mem_singleton] at hmem
  rcases hmem with hrest | hT
  · rcases hrest with hA | hI
    · simp only [phaseAGuardsFrom, List.mem_map] at hA
      rcases hA with ⟨k, hk, rfl⟩
      simp [upperCheck]
    · simp only [sourceInterpolationSchedule, allInterpolationChecks,
        List.mem_flatMap, List.mem_map] at hI
      rcases hI with ⟨i, hi, j, hj, rfl⟩
      simp [interpolationCheck]
  · subst check
    simp [sourceTerminalGuard, terminalCheck]

theorem source_phaseA_guard_mem (inst : PositiveInstance 2 d x0)
    (M D : ℝ) (n k : ℕ) (hk : k < n) :
    exactGuardCheck .upperModel inst.oracle
      ((sourcePhaseAData inst M D n).y k)
      ((sourcePhaseAData inst M D n).x (k + 1)) ∈
      sourceGuardSchedule inst M n := by
  apply List.mem_append_left
  apply List.mem_append_left
  unfold phaseAGuardsFrom sourcePhaseAData
  simp only [Nat.zero_add, List.mem_map]
  refine ⟨k, List.mem_range.mpr hk, ?_⟩
  rfl

theorem source_interpolation_guard_mem (inst : PositiveInstance 2 d x0)
    (M : ℝ) (n i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) :
    exactGuardCheck .interpolation inst.oracle
      ((sourcePhaseBData inst M n (sourceU inst M n)).u i)
      ((sourcePhaseBData inst M n (sourceU inst M n)).u j) ∈
      sourceGuardSchedule inst M n := by
  apply List.mem_append_left
  apply List.mem_append_right
  unfold sourceInterpolationSchedule allInterpolationChecks sourcePhaseBData sourceU
  simp only [List.mem_flatMap, List.mem_map]
  refine ⟨i, List.mem_range.mpr (by omega), j, List.mem_range.mpr (by omega), ?_⟩
  rfl

theorem fullShape_failure {inst : PositiveInstance 2 d x0}
    {eps M : ℝ} {n : ℕ} {report : TrialReport d}
    (hshape : FullReportShape inst eps M n report)
    {failed : ObservableGuardCheck d} (hout : report.outcome = .scale failed) :
    FailureLedger 2 M report failed := by
  rcases hshape with hA | hI | hT | hS | hR
  · rcases hA with ⟨r, hr, g, hledger, rest⟩
    have heq : g = failed := by
      rw [hledger.1] at hout
      injection hout
    subst g
    exact hledger
  · rcases hI with ⟨g, hledger, rest⟩
    have heq : g = failed := by rw [hledger.1] at hout; injection hout
    subst g
    exact hledger
  · rcases hT with ⟨g, hledger, rest⟩
    have heq : g = failed := by rw [hledger.1] at hout; injection hout
    subst g
    exact hledger
  · rcases hS with ⟨terminal, hs, rest⟩
    rw [hs] at hout
    cases hout
  · rcases hR with ⟨terminal, hr, rest⟩
    rw [hr] at hout
    cases hout

theorem source_operational_contract (inst : PositiveInstance 2 d x0)
    (eps M D : ℝ) (n : ℕ) (hM : 0 < M) (hn : 1 ≤ n)
    (report : TrialReport d) (hshape : FullReportShape inst eps M n report) :
    EuclideanTrialOperationalContract x0 M D inst report
      (sourcePhaseAData inst M D n)
      (sourcePhaseBData inst M n (sourceU inst M n)) := by
  have hlists := source_lists_eq_carriers inst M D n
  have hpref := fullShape_prefixes hshape
  refine ⟨rfl, rfl, rfl, rfl, sourcePhaseA_dynamics inst M D n hM,
    rfl, rfl, rfl, sourcePhaseB_dynamics inst M n (sourceU inst M n) hM hn,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro check hmem
    exact sourceSchedule_kinds inst M n check
      (hpref.2.subset hmem)
  · simpa [hlists.2] using hpref.2
  · simpa [hlists.1] using hpref.1
  · intro failed hout
    rcases hshape with hA | hI | hT | hS | hR
    · left
      rcases hA with ⟨r, hr, g, hledger, hpairs, hkind, htp, hgp, htlen, hglen⟩
      have heq : g = failed := by rw [hledger.1] at hout; injection hout
      subst g
      refine ⟨hkind, r, hr, ?_, ?_⟩
      · rw [← hlists.2]
        have heq := List.prefix_iff_eq_take.mp hgp
        rw [heq, hglen]
      · rw [← hlists.1]
        have heq := List.prefix_iff_eq_take.mp htp
        rw [heq, htlen]
    · right; left
      rcases hI with ⟨g, hledger, hpairs, hkind, htrace, hguards⟩
      have heq : g = failed := by rw [hledger.1] at hout; injection hout
      subst g
      refine ⟨hkind, ?_⟩
      rw [← hlists.1, htrace]
      have hp : phaseATraceFrom inst M 0 n ++ sourceNewTrace inst M n <+:
          sourcePlannedTrace inst M n := by
        unfold sourcePlannedTrace
        exact List.prefix_append _ _
      have heq := List.prefix_iff_eq_take.mp hp
      have hlen : (phaseATraceFrom inst M 0 n ++ sourceNewTrace inst M n).length =
          2 * n + n := by simp
      simpa [hlen] using heq
    · right; right
      rcases hT with ⟨g, hledger, hpairs, hkind, htrace, hguards⟩
      have heq : g = failed := by rw [hledger.1] at hout; injection hout
      subst g
      exact ⟨hkind, by simpa [hlists.2] using hguards,
        by simpa [hlists.1] using htrace⟩
    · rcases hS with ⟨terminal, hs, rest⟩
      rw [hs] at hout
      cases hout
    · rcases hR with ⟨terminal, hr, rest⟩
      rw [hr] at hout
      cases hout
  · intro terminal hout
    rcases hshape with hA | hI | hT | hS | hR
    · rcases hA with ⟨r, hr, g, hledger, rest⟩
      rw [hledger.1] at hout
      cases hout
    · rcases hI with ⟨g, hledger, rest⟩
      rw [hledger.1] at hout
      cases hout
    · rcases hT with ⟨g, hledger, rest⟩
      rw [hledger.1] at hout
      cases hout
    · rcases hS with ⟨on, hs, hon, htrace, hguards, hall, hn⟩
      have heq : on = terminal := by rw [hs] at hout; injection hout
      subst terminal
      refine ⟨?_, by simpa [hlists.1] using htrace,
        by simpa [hlists.2] using hguards, ?_, ?_⟩
      · simpa [sourcePhaseBData, sourceU] using hon
      · intro k hk
        exact ⟨exactGuardCheck .upperModel inst.oracle
          ((sourcePhaseAData inst M D n).y k)
          ((sourcePhaseAData inst M D n).x (k + 1)),
          by simpa [hguards] using source_phaseA_guard_mem inst M D n k hk,
          rfl, rfl, rfl⟩
      · intro i hi j hj
        exact ⟨exactGuardCheck .interpolation inst.oracle
          ((sourcePhaseBData inst M n (sourceU inst M n)).u i)
          ((sourcePhaseBData inst M n (sourceU inst M n)).u j),
          by simpa [hguards] using source_interpolation_guard_mem inst M n i j hi hj,
          rfl, rfl, rfl⟩
    · rcases hR with ⟨on, hr, rest⟩
      rw [hr] at hout
      cases hout
  · intro terminal hout
    rcases hshape with hA | hI | hT | hS | hR
    · rcases hA with ⟨r, hr, g, hledger, rest⟩
      rw [hledger.1] at hout
      cases hout
    · rcases hI with ⟨g, hledger, rest⟩
      rw [hledger.1] at hout
      cases hout
    · rcases hT with ⟨g, hledger, rest⟩
      rw [hledger.1] at hout
      cases hout
    · rcases hS with ⟨on, hs, rest⟩
      rw [hs] at hout
      cases hout
    · rcases hR with ⟨on, hr, hon, htrace, hguards, hall, hn⟩
      have heq : on = terminal := by rw [hr] at hout; injection hout
      subst terminal
      refine ⟨by simpa [hlists.1] using htrace, ?_,
        by simpa [hlists.2] using hguards, ?_, ?_, ?_⟩
      · simpa [sourcePhaseBData, sourceU] using hon
      · intro k hk
        exact ⟨exactGuardCheck .upperModel inst.oracle
          ((sourcePhaseAData inst M D n).y k)
          ((sourcePhaseAData inst M D n).x (k + 1)),
          by simpa [hguards] using source_phaseA_guard_mem inst M D n k hk,
          rfl, rfl, rfl⟩
      · intro i hi j hj
        exact ⟨exactGuardCheck .interpolation inst.oracle
          ((sourcePhaseBData inst M n (sourceU inst M n)).u i)
          ((sourcePhaseBData inst M n (sourceU inst M n)).u j),
          by simpa [hguards] using source_interpolation_guard_mem inst M n i j hi hj,
          rfl, rfl, rfl⟩
      · exact ⟨sourceTerminalGuard inst M n, by
          rw [hguards]
          simp [sourceGuardSchedule], rfl, rfl, rfl⟩

end Stage1E03
end V7

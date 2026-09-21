/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage1E03.AnalyticBridge

/-!
Correctness certificates for all possible reports of the Euclidean local trial.
-/

namespace V7
namespace Stage1E03

/-- Classical proposition decisions used locally by the trace certificate. -/
noncomputable local instance certificatePropDecidable (q : Prop) : Decidable q :=
  Classical.propDecidable q

theorem sourcePlannedTrace_exact (inst : PositiveInstance 2 d x0)
    (M : ℝ) (n : ℕ) : TraceExact inst.oracle (sourcePlannedTrace inst M n) := by
  intro obs hobs
  simp only [sourcePlannedTrace, List.mem_append, List.mem_singleton] at hobs
  rcases hobs with hpre | hT
  · rcases hpre with hA | hB
    · simp only [phaseATraceFrom, List.mem_flatMap] at hA
      rcases hA with ⟨k, hk, hpair⟩
      simp only [List.mem_cons] at hpair
      rcases hpair with hfirst | hsecond
      · subst obs; rfl
      · rcases hsecond with hsecond | hnil
        · subst obs; rfl
        · contradiction
    · simp only [sourceNewTrace, List.mem_map] at hB
      rcases hB with ⟨k, hk, hobs⟩
      subst obs
      rfl
  · subst obs
    rfl

theorem fullShape_trace_exact (inst : PositiveInstance 2 d x0)
    (eps M : ℝ) (n : ℕ) (report : TrialReport d)
    (hshape : FullReportShape inst eps M n report) :
    TraceExact inst.oracle report.trace := by
  intro obs hmem
  exact sourcePlannedTrace_exact inst M n obs
    ((fullShape_prefixes hshape).1.subset hmem)

theorem fullShape_guard_data (inst : PositiveInstance 2 d x0)
    (eps M : ℝ) (n : ℕ) (cached : CachedPair d)
    (hcached : cached.observation = inst.oracle.observe x0)
    (report : TrialReport d) (hshape : FullReportShape inst eps M n report) :
    GuardDataExact cached inst.oracle report := by
  refine ⟨?_, ?_⟩
  · rw [hcached]
    rfl
  · intro check hmem
    have hpairs := fullShape_pairs hshape check hmem
    have htrace := fullShape_trace_exact inst eps M n report hshape
    have hexactx := htrace check.xPair hpairs.1
    have hexacty := htrace check.yPair hpairs.2
    refine ⟨?_, ?_, hexactx, hexacty⟩
    · exact Or.inr hpairs.1
    · exact Or.inr hpairs.2

theorem fullShape_outcome_exhaustive
      (report : TrialReport d) :
    TrialOutcomeExhaustive report := by
  cases h : report.outcome with
  | success obs => exact Or.inl ⟨obs, h⟩
  | scale check => exact Or.inr (Or.inl ⟨check, h⟩)
  | radius obs => exact Or.inr (Or.inr ⟨obs, h⟩)

theorem fullShape_scale_lt (inst : PositiveInstance 2 d x0)
    (eps M : ℝ) (n : ℕ) (heps : 0 < eps) (hM : 0 < M)
    (hG : eps < lpNorm 2 (inst.oracle.gradient x0))
    (report : TrialReport d) (hshape : FullReportShape inst eps M n report)
    (failed : ObservableGuardCheck d) (hout : report.outcome = .scale failed) :
    M < inst.L := by
  have hledger := fullShape_failure hshape hout
  have hmem : failed ∈ report.checkedGuards := by
    rcases List.getLast?_eq_some_iff.mp hledger.2.1 with ⟨front, hfront⟩
    rw [hfront]
    simp
  have hpairs := fullShape_pairs hshape failed hmem
  have htrace := fullShape_trace_exact inst eps M n report hshape
  have hfail := guardFails_of_not_checkHolds 2 M inst.oracle failed
    (htrace failed.xPair hpairs.1) (htrace failed.yPair hpairs.2) hledger.2.2.2
  let P := legacyInstance inst eps heps hG
  by_contra hnot
  have hLM : inst.L ≤ M := le_of_not_gt hnot
  cases hk : failed.kind with
  | upperModel =>
      have hf : ¬ UpperModelGuard 2 M inst.oracle
          failed.xPair.point failed.yPair.point := by
        simpa [GuardFails, ObservableGuardCheck.failure, hk] using hfail
      exact hf (upperModelGuard_of_scale_ge (by norm_num) inst hLM rfl _ _)
  | gradient =>
      have hallowed := sourceSchedule_kinds inst M n failed
        ((fullShape_prefixes hshape).2.subset hmem)
      simp [hk] at hallowed
  | cocoercivity =>
      have hallowed := sourceSchedule_kinds inst M n failed
        ((fullShape_prefixes hshape).2.subset hmem)
      simp [hk] at hallowed
  | interpolation =>
      have hf : ¬ EuclideanInterpolationGuard M inst.oracle
          failed.xPair.point failed.yPair.point := by
        simpa [GuardFails, ObservableGuardCheck.failure, hk] using hfail
      have hLMP : P.L ≤ M := by
        dsimp only [P]
        simpa using hLM
      have hold := O3.euclideanInterpolationGuard_holds_of_le P hM hLMP
        failed.xPair.point failed.yPair.point
      dsimp only [P] at hold
      exact hf ((euclideanInterpolationGuard_iff_historical M inst.oracle _ _).2
        (by simpa using hold))
  | terminalDescent =>
      rcases hshape with hA | hI | hT | hS | hR
      · rcases hA with ⟨r, hr, g, hledgerA, hpairsA, hkind, rest⟩
        have heg : g = failed := by rw [hledgerA.1] at hout; injection hout
        subst g; rw [hkind] at hk; cases hk
      · rcases hI with ⟨g, hl, hp, hkind, rest⟩
        have heg : g = failed := by rw [hl.1] at hout; injection hout
        subst g; rw [hkind] at hk; cases hk
      · rcases hT with ⟨g, hl, hp, hkind, htraceR, hguards⟩
        have heg : g = failed := by rw [hl.1] at hout; injection hout
        subst g
        have hlast := hl.2.1
        rw [hguards] at hlast
        have heq : failed = sourceTerminalGuard inst M n := by
          simpa [sourceGuardSchedule] using hlast.symm
        subst failed
        have hLMP : P.L ≤ M := by
          dsimp only [P]
          simpa using hLM
        have hold := O3.ogmgTerminalDescentCheck_holds_of_le P
          (O3.stage9ExecutionConfig n inst.oracle M (sourceU inst M n))
          rfl rfl hLMP
        have hsource := (O3.ogmgTerminalDescentCheck_source_iff
          (O3.stage9ExecutionConfig n inst.oracle M (sourceU inst M n)) hM).mp hold
        exact hledger.2.2.2 (by
          simpa [sourceTerminalGuard, terminalCheck, CheckHolds,
            O3.ogmgTerminalObservation, O3.ogmgObservation,
            O3.ogmgGradient, O3.PairOracle.observe,
            O3.stage9ExecutionConfig] using hsource)
      · rcases hS with ⟨o, ho, rest⟩; rw [ho] at hout; cases hout
      · rcases hR with ⟨o, ho, rest⟩; rw [ho] at hout; cases hout

theorem holds_imply_not_fails (inst : PositiveInstance 2 d x0)
    (eps M : ℝ) (n : ℕ) (cached : CachedPair d)
    (hcached : cached.observation = inst.oracle.observe x0)
    (report : TrialReport d) (hshape : FullReportShape inst eps M n report)
    (hall : ∀ check ∈ report.checkedGuards, CheckHolds 2 M check) :
    ∀ check ∈ report.checkedGuards,
      ¬ GuardFails 2 M inst.oracle check.failure := by
  have hdata := fullShape_guard_data inst eps M n cached hcached report hshape
  intro check hmem
  exact not_guardFails_of_checkHolds 2 M inst.oracle check
    (hdata.2 check hmem).2.2.1 (hdata.2 check hmem).2.2.2 (hall check hmem)

theorem source_phaseA_accepted (inst : PositiveInstance 2 d x0)
    (eps M D : ℝ) (n : ℕ) (heps : 0 < eps)
    (hG : eps < lpNorm 2 (inst.oracle.gradient x0))
    (report : TrialReport d)
    (hall : ∀ check ∈ report.checkedGuards, CheckHolds 2 M check)
    (hguards : report.checkedGuards = sourceGuardSchedule inst M n) :
    O3.EuclideanEstimateAccepted (legacyInstance inst eps heps hG) M n := by
  intro k hk
  have hmem := source_phaseA_guard_mem inst M D n k hk
  rw [← hguards] at hmem
  have hc := hall _ hmem
  have hstatek := sourceEstimateState_eq_legacy inst eps M heps hG k
  have hstateS := sourceEstimateState_eq_legacy inst eps M heps hG (k + 1)
  simp only [sourcePhaseAData] at hc
  rw [hstatek, hstateS] at hc
  simpa [CheckHolds, exactGuardCheck, O3.euclideanEstimateGuard,
    O3.upperModelGuard_holds_iff, O3.euclideanEstimateObservation,
    O3.euclideanEstimateQuery, O3.euclideanEstimateMinimizer,
    O3.AdmissibleInstance.oracle, O3.PairOracle.observe,
    estimateQuery] using hc

theorem source_interpolation_accepted (inst : PositiveInstance 2 d x0)
    (eps M : ℝ) (n : ℕ) (heps : 0 < eps)
    (hG : eps < lpNorm 2 (inst.oracle.gradient x0))
    (report : TrialReport d)
    (hall : ∀ check ∈ report.checkedGuards, CheckHolds 2 M check)
    (hguards : report.checkedGuards = sourceGuardSchedule inst M n) :
    O3.OGMGAllInterpolationGuardsHold
      (O3.stage9ExecutionConfig n (legacyInstance inst eps heps hG).oracle M
        (O3.euclideanEstimateState (legacyInstance inst eps heps hG) M n).accelerated) := by
  rw [O3.ogmgAllInterpolationGuardsHold_iff]
  intro i j
  have hi : i.val ≤ n := by
    simpa [O3.stage9ExecutionConfig] using Nat.le_of_lt_succ i.isLt
  have hj : j.val ≤ n := by
    simpa [O3.stage9ExecutionConfig] using Nat.le_of_lt_succ j.isLt
  have hmem := source_interpolation_guard_mem inst M n i.val j.val hi hj
  rw [← hguards] at hmem
  have hc := hall _ hmem
  simp only [sourcePhaseBData] at hc
  rw [sourceU_eq_legacy inst eps M heps hG n] at hc
  simpa [CheckHolds, exactGuardCheck, O3.interpolationGuard_holds_iff,
    O3.ogmgInterpolationCheck, O3.ogmgDataObservation,
    O3.stage9ExecutionConfig, sourcePhaseBData,
    O3.AdmissibleInstance.oracle,
    O3.PairOracle.observe] using hc

theorem source_terminal_accepted (inst : PositiveInstance 2 d x0)
    (eps M : ℝ) (n : ℕ) (heps : 0 < eps) (hM : 0 < M)
    (hG : eps < lpNorm 2 (inst.oracle.gradient x0))
    (report : TrialReport d)
    (hall : ∀ check ∈ report.checkedGuards, CheckHolds 2 M check)
    (hguards : report.checkedGuards = sourceGuardSchedule inst M n) :
    (O3.ogmgTerminalDescentCheck
      (O3.stage9ExecutionConfig n (legacyInstance inst eps heps hG).oracle M
        (O3.euclideanEstimateState (legacyInstance inst eps heps hG) M n).accelerated)).Holds := by
  have hmem : sourceTerminalGuard inst M n ∈ report.checkedGuards := by
    rw [hguards]
    simp [sourceGuardSchedule]
  have hc := hall _ hmem
  rw [O3.ogmgTerminalDescentCheck_source_iff _ hM]
  simp only [sourceTerminalGuard] at hc
  rw [sourceU_eq_legacy inst eps M heps hG n] at hc
  simpa [sourceTerminalGuard, terminalCheck, CheckHolds,
    O3.stage9ExecutionConfig,
    O3.ogmgTerminalObservation, O3.ogmgObservation, O3.ogmgGradient,
    O3.AdmissibleInstance.oracle, O3.PairOracle.observe] using hc

theorem fullShape_radius_lt (inst : PositiveInstance 2 d x0)
    (eps M D : ℝ) (n : ℕ) (heps : 0 < eps) (hM : 0 < M) (hD : 0 < D)
    (hn : 1 ≤ n) (hnEq : n = horizon eps M D)
    (hkappa : 1 ≤ M * D / eps)
    (hG : eps < lpNorm 2 (inst.oracle.gradient x0))
    (report : TrialReport d) (hshape : FullReportShape inst eps M n report)
    (terminal : Observation d) (hout : report.outcome = .radius terminal) :
    D < inst.R := by
  rcases hshape with hA | hI | hT | hS | hR
  · rcases hA with ⟨r, hr, g, hl, rest⟩; rw [hl.1] at hout; cases hout
  · rcases hI with ⟨g, hl, rest⟩; rw [hl.1] at hout; cases hout
  · rcases hT with ⟨g, hl, rest⟩; rw [hl.1] at hout; cases hout
  · rcases hS with ⟨o, ho, rest⟩; rw [ho] at hout; cases hout
  · rcases hR with ⟨on, hr, hon, htrace, hguards, hpairs, hall, hnorm⟩
    have heq : on = terminal := by rw [hr] at hout; injection hout
    subst terminal
    let P := legacyInstance inst eps heps hG
    by_contra hnot
    have hDR : P.radius ≤ D := by
      dsimp only [P]
      simpa using le_of_not_gt hnot
    have hDRV7 : inst.R ≤ D := by
      dsimp only [P] at hDR
      simpa using hDR
    have hbound := source_current_gradient_bound inst M D n hM hD hn
      hDRV7 report hall hguards
    have hbudget := horizon_gradient_budget heps hM hD hkappa
    have hgood : lpNorm 2 on.gradient ≤ eps := by
      have hbound' : lpNorm 2 on.gradient ≤
          2 * Real.sqrt 2 * M * D /
            (((n : ℝ) + 1) * ((n : ℝ) + 1)) := by
        simpa [hon, sourcePhaseBData, O3.PairOracle.observe,
          O3.stage9ExecutionConfig] using hbound
      exact hbound'.trans (by
        rw [hnEq]
        simpa using hbudget)
    linarith

theorem source_trial_certificate (inst : PositiveInstance 2 d x0)
    (eps M D : ℝ) (n : ℕ) (heps : 0 < eps) (hM : 0 < M) (hD : 0 < D)
    (hn : 1 ≤ n) (hnEq : n = horizon eps M D)
    (hkappa : 1 ≤ M * D / eps)
    (hG : eps < lpNorm 2 (inst.oracle.gradient x0))
    (cached : CachedPair d)
    (hcached : cached.observation = inst.oracle.observe x0)
    (report : TrialReport d) (hshape : FullReportShape inst eps M n report) :
    TrialCertificate eps 2 M D inst.L inst.R cached inst.oracle report := by
  have htrace := fullShape_trace_exact inst eps M n report hshape
  have hdata := fullShape_guard_data inst eps M n cached hcached report hshape
  refine ⟨htrace, hdata, fullShape_outcome_exhaustive report,
    ?_, ?_, ?_⟩
  · intro terminal hout
    rcases hshape with hA | hI | hT | hS | hR
    · rcases hA with ⟨r, hr, g, hl, rest⟩; rw [hl.1] at hout; cases hout
    · rcases hI with ⟨g, hl, rest⟩; rw [hl.1] at hout; cases hout
    · rcases hT with ⟨g, hl, rest⟩; rw [hl.1] at hout; cases hout
    · rcases hS with ⟨on, hs, hon, htraceR, hguards, hpairs, hall, hnorm⟩
      have heq : on = terminal := by rw [hs] at hout; injection hout
      subst terminal
      have hmem : on ∈ report.trace := by
        rw [htraceR]
        rw [hon]
        apply List.mem_append_left
        exact source_u_mem_preterminal inst M n n hn (le_refl n)
      refine ⟨hmem, htrace on hmem, ?_, ?_⟩
      · exact holds_imply_not_fails inst eps M n cached hcached report
          (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨on, hs, hon, htraceR, hguards, hpairs, hall, hnorm⟩)))) hall
      · simpa only [show conjugateExponent 2 = 2 by
          norm_num [conjugateExponent, O3.conjugateExponent,
            Real.conjExponent]] using hnorm
    · rcases hR with ⟨on, hr, rest⟩; rw [hr] at hout; cases hout
  · intro failed hout
    have hl := fullShape_failure hshape hout
    have hmem : failed ∈ report.checkedGuards := by
      rcases List.getLast?_eq_some_iff.mp hl.2.1 with ⟨front, hfront⟩
      rw [hfront]
      simp
    refine ⟨hmem, hl.2.1, ?_, ?_,
      fullShape_scale_lt inst eps M n heps hM hG report hshape failed hout⟩
    · intro check hcheck
      have hmemAll : check ∈ report.checkedGuards :=
        List.dropLast_subset _ hcheck
      exact not_guardFails_of_checkHolds 2 M inst.oracle check
        (hdata.2 check hmemAll).2.2.1 (hdata.2 check hmemAll).2.2.2
        (hl.2.2.1 check hcheck)
    · exact guardFails_of_not_checkHolds 2 M inst.oracle failed
        (hdata.2 failed hmem).2.2.1 (hdata.2 failed hmem).2.2.2 hl.2.2.2
  · intro terminal hout
    rcases hshape with hA | hI | hT | hS | hR
    · rcases hA with ⟨r, hr, g, hl, rest⟩; rw [hl.1] at hout; cases hout
    · rcases hI with ⟨g, hl, rest⟩; rw [hl.1] at hout; cases hout
    · rcases hT with ⟨g, hl, rest⟩; rw [hl.1] at hout; cases hout
    · rcases hS with ⟨on, hs, rest⟩; rw [hs] at hout; cases hout
    · rcases hR with ⟨on, hr, hon, htraceR, hguards, hpairs, hall, hnorm⟩
      have heq : on = terminal := by rw [hr] at hout; injection hout
      subst terminal
      have hmem : on ∈ report.trace := by
        rw [htraceR]
        rw [hon]
        apply List.mem_append_left
        exact source_u_mem_preterminal inst M n n hn (le_refl n)
      refine ⟨hmem, htrace on hmem, ?_, ?_, ?_⟩
      · exact holds_imply_not_fails inst eps M n cached hcached report
          (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨on, hr, hon, htraceR, hguards, hpairs, hall, hnorm⟩)))) hall
      · simpa only [show conjugateExponent 2 = 2 by
          norm_num [conjugateExponent, O3.conjugateExponent,
            Real.conjExponent]] using hnorm
      · exact fullShape_radius_lt inst eps M D n heps hM hD hn hnEq hkappa
          hG report (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨on, hr, hon, htraceR, hguards, hpairs, hall, hnorm⟩)))) on hr

end Stage1E03
end V7

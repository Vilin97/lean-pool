/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage8Main.RuntimeMachine

/-!
Selection and certification of the local trial for each runtime exponent regime.
-/

namespace V7.Stage8Main

/-- The local query-cost coefficient for the runtime's exponent regime. -/
noncomputable def runtimeCoefficient (data : RuntimeData d) : ℝ :=
  if hp2 : data.input.p < 2 then
    4 / Real.sqrt (data.input.p - 1) + 2
  else if hpEq : data.input.p = 2 then
    euclideanConstant
  else
    aboveConstant data.input.p
      (lt_of_le_of_ne (le_of_not_gt hp2) (Ne.symm hpEq))

theorem RuntimeControllerState.D_ge_base (data : RuntimeData d)
    (state : RuntimeControllerState d) :
    state.D data ≥ data.G / state.M data := by
  have hbase : 0 ≤ data.G / state.M data :=
    (div_pos data.hG (state.M_pos data)).le
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ state.radiusLevel :=
    one_le_pow₀ (by norm_num)
  calc
    data.G / state.M data ≤ (2 : ℝ) ^ state.radiusLevel *
        (data.G / state.M data) :=
      le_mul_of_one_le_left hbase hpow
    _ = state.D data := by
      simp only [RuntimeControllerState.D]
      ring

/-- A local report together with its execution, correctness, guard, and query-cost certificates. -/
structure LocalRunSpec (data : RuntimeData d)
    (state : RuntimeControllerState d)
    (inst : PositiveInstance data.input.p d data.input.x0) where
  /-- The report produced by the certified local run. -/
  report : TrialReport d
  executes : (runtimeTrial data state).Executes (state.M data) (state.D data)
    data.cached inst.oracle report
  certificate : TrialCertificate data.input.eps data.input.p
    (state.M data) (state.D data) inst.L inst.R data.cached inst.oracle report
  complete : GuardLedgerComplete data.input.p report report.checkedGuards
  trace_nonempty : report.trace ≠ []
  calls_bound : (report.calls : ℝ) ≤ runtimeCoefficient data *
    (state.M data * state.D data / data.input.eps) ^
      (localCostExponent data.input.p)

private theorem report_trace_nonempty_of_accounting
    {eps p M D L R : ℝ} {cached : CachedPair d} {oracle : PairOracle d}
    {report : TrialReport d}
    (hcert : TrialCertificate eps p M D L R cached oracle report)
    (haccount : report.consecutiveGuardAccounting) : report.trace ≠ [] := by
  intro hnil
  rcases hcert with ⟨_, _, _, hsuccess, hscale, hradius⟩
  cases hout : report.outcome with
  | success terminal =>
      have hmem := (hsuccess terminal hout).1
      simp [hnil] at hmem
  | radius terminal =>
      have hmem := (hradius terminal hout).1
      simp [hnil] at hmem
  | scale failed =>
      have hmem := (hscale failed hout).1
      have hlen : report.checkedGuards.length = 0 := by
        simpa [TrialReport.consecutiveGuardAccounting, hout,
          TrialReport.calls, hnil] using haccount
      have hne : report.checkedGuards ≠ [] := by
        intro hg
        simp [hg] at hmem
      have hpos : 0 < report.checkedGuards.length := by
        apply Nat.pos_of_ne_zero
        intro hz
        exact hne (List.eq_nil_of_length_eq_zero hz)
      omega

private theorem euclidean_contract_trace_nonempty
    {x0 : Point d} {M D : ℝ} {inst : PositiveInstance 2 d x0}
    {report : TrialReport d} {m n : ℕ}
    {phaseA : EuclideanGapData d m} {phaseB : OGMGData d n}
    (hm : 1 ≤ m) (hn : n = m)
    (hcontract : EuclideanTrialOperationalContract x0 M D inst report phaseA phaseB) :
    report.trace ≠ [] := by
  intro hnil
  rcases hcontract with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, hstop, hsuccess, hradius⟩
  cases hout : report.outcome with
  | success terminal =>
      have htrace := (hsuccess terminal hout).2.1
      have hlen : 0 < report.trace.length := by
        rw [htrace]
        simp [euclideanPlannedTrace]
      simp [hnil] at hlen
  | radius terminal =>
      have htrace := (hradius terminal hout).1
      have hlen : 0 < report.trace.length := by
        rw [htrace]
        simp [euclideanPlannedTrace]
      simp [hnil] at hlen
  | scale failed =>
      rcases hstop failed hout with hupper | hinterp | hterminal
      · rcases hupper with ⟨_, k, hk, _, htrace⟩
        have hlen : 0 < report.trace.length := by
          rw [htrace]
          simp [euclideanPlannedTrace]
        simp [hnil] at hlen
      · have htrace := hinterp.2
        have hlen : 0 < report.trace.length := by
          rw [htrace]
          simp [euclideanPlannedTrace, hn]
          omega
        simp [hnil] at hlen
      · have htrace := hterminal.2.2
        have hlen : 0 < report.trace.length := by
          rw [htrace]
          simp [euclideanPlannedTrace]
        simp [hnil] at hlen

private theorem coco_complete {p : ℝ} (hp2 : p ≠ 2)
    {report : TrialReport d}
    (hkinds : CheckedGuardsHaveKinds report [.cocoercivity]) :
    GuardLedgerComplete p report report.checkedGuards := by
  refine ⟨List.prefix_refl _, ?_, ?_⟩
  · intro check hcheck
    have hk := hkinds check hcheck
    simp only [List.mem_singleton] at hk
    simp [GuardAllowedInRegime, hp2, hk]
  · intro terminal _
    rfl

private theorem euclidean_complete {report : TrialReport d}
    (hkinds : CheckedGuardsHaveKinds report
      [.upperModel, .interpolation, .terminalDescent]) :
    GuardLedgerComplete 2 report report.checkedGuards := by
  refine ⟨List.prefix_refl _, ?_, ?_⟩
  · intro check hcheck
    have hk := hkinds check hcheck
    simpa [GuardAllowedInRegime] using hk
  · intro terminal _
    rfl

theorem runtimeTrial_spec (data : RuntimeData d)
    (state : RuntimeControllerState d)
    (inst : PositiveInstance data.input.p d data.input.x0)
    (hcached : data.cached.observation = inst.oracle.observe data.input.x0)
    (hlarge : data.input.eps < lpNorm (conjugateExponent data.input.p)
      (inst.oracle.gradient data.input.x0)) :
    Nonempty (LocalRunSpec data state inst) := by
  have hDbase := state.D_ge_base data
  have hGvalue : data.G = lpNorm (conjugateExponent data.input.p)
      (inst.oracle.gradient data.input.x0) := by
    rw [data.G_eq, hcached]
    rfl
  rw [hGvalue] at hDbase
  by_cases hp2 : data.input.p < 2
  · obtain ⟨report, w, hexec, hcert, hcontract, _, hcalls⟩ :=
      belowTrialFor_spec data.input.p data.hp hp2 data.input.eps
        (state.M data) (state.D data) data.heps (state.M_pos data)
        (state.D_pos data) data.input.x0 data.cached inst hcached hlarge hDbase
    rcases hcontract with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hkinds, _, haccount, _⟩
    refine ⟨⟨report, ?_, hcert, ?_, ?_, ?_⟩⟩
    · simpa [runtimeTrial, hp2] using hexec
    · exact coco_complete (ne_of_lt hp2) hkinds
    · exact report_trace_nonempty_of_accounting hcert haccount
    · simpa [runtimeCoefficient, hp2, localCostExponent, le_of_lt hp2,
        Real.sqrt_eq_rpow] using hcalls
  · by_cases hpEq : data.input.p = 2
    · let inst2 : PositiveInstance 2 d data.input.x0 :=
        { oracle := inst.oracle
          L := inst.L
          L_pos := inst.L_pos
          coordinateGradient := inst.coordinateGradient
          convex := inst.convex
          minimizerNonempty := inst.minimizerNonempty
          smooth := by simpa [hpEq] using inst.smooth }
      have hq : conjugateExponent (2 : ℝ) = 2 := by
        norm_num [conjugateExponent, O3.conjugateExponent, Real.conjExponent]
      have hlarge2 : data.input.eps <
          lpNorm 2 (inst2.oracle.gradient data.input.x0) := by
        simpa [inst2, hpEq, hq] using hlarge
      have hDbase2 : state.D data ≥
          lpNorm 2 (inst2.oracle.gradient data.input.x0) / state.M data := by
        simpa [inst2, hpEq, hq] using hDbase
      obtain ⟨hmEq, hnEq, hspec⟩ := euclideanTrialFor_spec data.input.eps
        (state.M data) (state.D data) data.heps (state.M_pos data)
        (state.D_pos data) data.input.x0 data.cached
      obtain ⟨report, phaseA, phaseB, hexec, hcert, hcontract, _, hcalls⟩ :=
        hspec inst2 (by simpa [inst2] using hcached) hlarge2 hDbase2
      have hm : 1 ≤ euclideanM data.input.eps (state.M data) (state.D data)
          data.heps (state.M_pos data) (state.D_pos data)
          data.input.x0 data.cached := by
        rw [hmEq]
        apply V7.Stage1E03.one_le_horizon
        have hMD : data.input.eps < state.M data * state.D data := by
          have hmul := mul_le_mul_of_nonneg_left hDbase2 (state.M_pos data).le
          have hcancel : state.M data *
              (lpNorm 2 (inst2.oracle.gradient data.input.x0) / state.M data) =
              lpNorm 2 (inst2.oracle.gradient data.input.x0) := by
            field_simp [(state.M_pos data).ne']
          rw [hcancel] at hmul
          linarith
        exact (le_div_iff₀ data.heps).2 (by simpa using hMD.le)
      have hkinds := hcontract.2.2.2.2.2.2.2.2.2.1
      refine ⟨⟨report, ?_, ?_, ?_,
        euclidean_contract_trace_nonempty hm hnEq hcontract, ?_⟩⟩
      · simpa [runtimeTrial, hp2, hpEq, inst2] using hexec
      · simpa [hpEq, inst2, PositiveInstance.R, minimizerDistance] using hcert
      · simpa [hpEq] using euclidean_complete hkinds
      · simpa [runtimeCoefficient, hp2, hpEq, localCostExponent,
        Real.sqrt_eq_rpow] using hcalls
    · have hpAbove : 2 < data.input.p :=
        lt_of_le_of_ne (le_of_not_gt hp2) (Ne.symm hpEq)
      obtain ⟨report, w, hexec, hcert, hcontract, hcalls⟩ :=
        aboveTrialFor_spec data.input.p hpAbove data.input.eps
          (state.M data) (state.D data) data.heps (state.M_pos data)
          (state.D_pos data) data.input.x0 data.cached inst hcached hlarge hDbase
      dsimp only [AboveTrialOperationalContract] at hcontract
      rcases hcontract with
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          hkinds, _, haccount, _⟩
      refine ⟨⟨report, ?_, hcert, ?_, ?_, ?_⟩⟩
      · simpa [runtimeTrial, hp2, hpEq] using hexec
      · exact coco_complete (ne_of_gt hpAbove) hkinds
      · exact report_trace_nonempty_of_accounting hcert haccount
      · simpa [runtimeCoefficient, hp2, hpEq, localCostExponent,
          not_le_of_gt hpAbove] using hcalls

end V7.Stage8Main

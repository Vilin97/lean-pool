/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.O3.Oracle

/-!
# Frozen outer curvature/radius controller

The executable object is a fuel-bounded deterministic controller.  Scale
failures double the curvature and reset the radius level; radius failures
double the tested radius; success is terminal.  Running states contain only
finite observations, guard reports, and exact counters.  Termination is proved
from the local-trial obligations and finite numerical search caps; it is not a
field of the controller state or of a certificate.
-/

namespace O3

/-- Inputs known to the outer controller after the anchor phase. -/
structure ControllerConfig where
  /-- The scale estimate at the controller's initial epoch. -/
  initialScale : ℝ
  /-- The initial gradient size used to convert scale levels into radii. -/
  gradientSizeAtStart : ℝ
  /-- The requested upper bound on the terminal gradient norm. -/
  eps : ℝ
  /-- Counted prefix calls (initial query and anchor probes). -/
  prefixCalls : ℕ

/-- The scale estimate after the specified number of dyadic doublings. -/
def ControllerConfig.scaleAt (cfg : ControllerConfig) (s : ℕ) : ℝ :=
  (2 : ℝ) ^ s * cfg.initialScale

/-- The radius at a given scale epoch and radius-doubling level. -/
noncomputable def ControllerConfig.radiusAt (cfg : ControllerConfig) (s j : ℕ) : ℝ :=
  (2 : ℝ) ^ j * cfg.gradientSizeAtStart / cfg.scaleAt s

/-- A running state.  Every report in `history` is a rejected trial. -/
structure ControllerState (d : ℕ) where
  /-- The current number of scale doublings. -/
  scaleEpoch : ℕ
  /-- The current number of radius doublings within the scale epoch. -/
  radiusLevel : ℕ
  /-- The total number of counted calls, including initialization. -/
  totalCalls : ℕ
  /-- The calls spent on trials already rejected by the controller. -/
  rejectedCalls : ℕ
  /-- The reports of all trials rejected before the current state. -/
  history : List (TrialReport d)

/-- Initialize both search levels at zero and retain the counted initialization cost. -/
def initialControllerState (cfg : ControllerConfig) : ControllerState d :=
  { scaleEpoch := 0
    radiusLevel := 0
    totalCalls := cfg.prefixCalls
    rejectedCalls := 0
    history := [] }

/-- The scale estimate selected by the current controller state. -/
def ControllerState.scale (cfg : ControllerConfig) (state : ControllerState d) : ℝ :=
  cfg.scaleAt state.scaleEpoch

/-- The radius selected by the current controller state. -/
noncomputable def ControllerState.radius (cfg : ControllerConfig) (state : ControllerState d) : ℝ :=
  cfg.radiusAt state.scaleEpoch state.radiusLevel

/-- A deterministic local guarded trial routine. -/
abbrev TrialRoutine (d : ℕ) := ℝ → ℝ → TrialReport d

/-- Terminal controller data; it contains no correctness proposition. -/
structure ControllerFinish (d : ℕ) where
  /-- The point returned by the successful terminal trial. -/
  point : Vec d
  /-- The total counted calls when the controller terminates. -/
  totalCalls : ℕ
  /-- The portion of the total cost spent on rejected trials. -/
  rejectedCalls : ℕ
  /-- The calls used by the successful terminal trial. -/
  terminalCalls : ℕ
  /-- The trial reports retained in the completed controller execution. -/
  history : List (TrialReport d)

/-- One controller transition either produces another running state or a completed result. -/
inductive ControllerStep (d : ℕ) where
  | next (state : ControllerState d)
  | done (finish : ControllerFinish d)

/-- One exact outer-controller transition. -/
def controllerStep (_cfg : ControllerConfig) (state : ControllerState d)
    (report : TrialReport d) : ControllerStep d :=
  let calls := report.calls
  match report.outcome with
  | .success x =>
      .done
        { point := x
          totalCalls := state.totalCalls + calls
          rejectedCalls := state.rejectedCalls
          terminalCalls := calls
          history := state.history ++ [report] }
  | .scale _ =>
      .next
        { scaleEpoch := state.scaleEpoch + 1
          radiusLevel := 0
          totalCalls := state.totalCalls + calls
          rejectedCalls := state.rejectedCalls + calls
          history := state.history ++ [report] }
  | .radius _ =>
      .next
        { scaleEpoch := state.scaleEpoch
          radiusLevel := state.radiusLevel + 1
          totalCalls := state.totalCalls + calls
          rejectedCalls := state.rejectedCalls + calls
          history := state.history ++ [report] }

/-- Run the local trial routine at the current scale and radius. -/
noncomputable def currentTrial (routine : TrialRoutine d) (cfg : ControllerConfig)
    (state : ControllerState d) : TrialReport d :=
  routine (state.scale cfg) (state.radius cfg)

/-- A bounded controller execution either exhausts its fuel or returns a successful result. -/
inductive ControllerRunResult (d : ℕ) where
  | exhausted (state : ControllerState d)
  | success (finish : ControllerFinish d)

/-- Explicit deterministic fuel-bounded execution; no termination is assumed. -/
noncomputable def runController (routine : TrialRoutine d) (cfg : ControllerConfig) :
    ℕ → ControllerState d → ControllerRunResult d
  | 0, state => .exhausted state
  | fuel + 1, state =>
      match controllerStep cfg state (currentTrial routine cfg state) with
      | .done finish => .success finish
      | .next state' => runController routine cfg fuel state'

/-- Exact invariant separating prefix, rejected, and terminal calls. -/
def ControllerState.Accounting (cfg : ControllerConfig)
    (state : ControllerState d) : Prop :=
  state.totalCalls = cfg.prefixCalls + state.rejectedCalls

/-- The total cost splits into initialization, rejected trials, and the terminal trial. -/
def ControllerFinish.Accounting (cfg : ControllerConfig)
    (finish : ControllerFinish d) : Prop :=
  finish.totalCalls =
    cfg.prefixCalls + finish.rejectedCalls + finish.terminalCalls

/-- Sum of calls recorded by a chronological list of local-trial reports. -/
def trialReportsCallCount (reports : List (TrialReport d)) : ℕ :=
  (reports.map TrialReport.calls).sum

/-- Running-state counters agree with the complete rejected-report history. -/
def ControllerState.HistoryAccounting (cfg : ControllerConfig)
    (state : ControllerState d) : Prop :=
  state.totalCalls = cfg.prefixCalls + trialReportsCallCount state.history ∧
  state.rejectedCalls = trialReportsCallCount state.history

/-- Terminal counters agree both with history and with rejected/terminal splitting. -/
def ControllerFinish.HistoryAccounting (cfg : ControllerConfig)
    (finish : ControllerFinish d) : Prop :=
  finish.totalCalls = cfg.prefixCalls + trialReportsCallCount finish.history ∧
  finish.totalCalls = cfg.prefixCalls + finish.rejectedCalls + finish.terminalCalls

theorem initialControllerState_accounting (cfg : ControllerConfig) :
    (initialControllerState cfg : ControllerState d).Accounting cfg := by
  simp [ControllerState.Accounting, initialControllerState]

theorem initialControllerState_historyAccounting (cfg : ControllerConfig) :
    (initialControllerState cfg : ControllerState d).HistoryAccounting cfg := by
  simp [ControllerState.HistoryAccounting, initialControllerState,
    trialReportsCallCount]

theorem controllerStep_accounting
    {cfg : ControllerConfig} {state : ControllerState d}
    (hstate : state.Accounting cfg) (report : TrialReport d) :
    match controllerStep cfg state report with
    | .next state' => state'.Accounting cfg
    | .done finish => finish.Accounting cfg := by
  rcases state with ⟨s, j, total, rejected, history⟩
  simp only [ControllerState.Accounting] at hstate
  subst total
  cases hout : report.outcome <;>
    simp [controllerStep, hout, ControllerState.Accounting,
      ControllerFinish.Accounting, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem runController_accounting
    (routine : TrialRoutine d) (cfg : ControllerConfig)
    {fuel : ℕ} {state : ControllerState d} (hstate : state.Accounting cfg) :
    match runController routine cfg fuel state with
    | .exhausted state' => state'.Accounting cfg
    | .success finish => finish.Accounting cfg := by
  induction fuel generalizing state with
  | zero => simpa [runController] using hstate
  | succ fuel ih =>
      have hstep := controllerStep_accounting hstate (currentTrial routine cfg state)
      cases htrans : controllerStep cfg state (currentTrial routine cfg state) with
      | done finish =>
          rw [runController, htrans]
          simpa [htrans] using hstep
      | next state' =>
          rw [runController, htrans]
          apply ih
          simpa [htrans] using hstep

theorem controllerStep_historyAccounting
    {cfg : ControllerConfig} {state : ControllerState d}
    (hstate : state.HistoryAccounting cfg) (report : TrialReport d) :
    match controllerStep cfg state report with
    | .next state' => state'.HistoryAccounting cfg
    | .done finish => finish.HistoryAccounting cfg := by
  rcases state with ⟨s, j, total, rejected, history⟩
  rcases hstate with ⟨htotal, hrejected⟩
  change total = cfg.prefixCalls + trialReportsCallCount history at htotal
  change rejected = trialReportsCallCount history at hrejected
  subst total
  subst rejected
  cases hout : report.outcome <;>
    simp [controllerStep, hout, ControllerState.HistoryAccounting,
      ControllerFinish.HistoryAccounting, trialReportsCallCount,
      Nat.add_assoc]

theorem runController_historyAccounting
    (routine : TrialRoutine d) (cfg : ControllerConfig)
    {fuel : ℕ} {state : ControllerState d} (hstate : state.HistoryAccounting cfg) :
    match runController routine cfg fuel state with
    | .exhausted state' => state'.HistoryAccounting cfg
    | .success finish => finish.HistoryAccounting cfg := by
  induction fuel generalizing state with
  | zero => simpa [runController] using hstate
  | succ fuel ih =>
      have hstep := controllerStep_historyAccounting hstate (currentTrial routine cfg state)
      cases htrans : controllerStep cfg state (currentTrial routine cfg state) with
      | done finish =>
          rw [runController, htrans]
          simpa [htrans] using hstep
      | next state' =>
          rw [runController, htrans]
          apply ih
          simpa [htrans] using hstep

/-- Relation consisting of one nonterminal deterministic controller step. -/
noncomputable def ControllerNext (routine : TrialRoutine d) (cfg : ControllerConfig)
    (state' state : ControllerState d) : Prop :=
  controllerStep cfg state (currentTrial routine cfg state) = .next state'

/-- Finite numerical caps for the two geometric searches. -/
structure ControllerCaps (cfg : ControllerConfig) (L R : ℝ) where
  /-- A scale epoch beyond which the guessed scale dominates the true smoothness scale. -/
  scaleCap : ℕ
  /-- A radius level sufficient to dominate the minimizer distance within the relevant epochs. -/
  radiusCap : ℕ
  scaleDominates : ∀ s, scaleCap ≤ s → L ≤ cfg.scaleAt s
  radiusDominates : ∀ s j, s ≤ scaleCap → radiusCap ≤ j → R ≤ cfg.radiusAt s j

/-- The two finite search caps follow from positivity; they are not supplied to the method. -/
theorem exists_controllerCaps (cfg : ControllerConfig) (L R : ℝ)
    (hM : 0 < cfg.initialScale) (hG : 0 < cfg.gradientSizeAtStart)
    (hR : 0 ≤ R) : Nonempty (ControllerCaps cfg L R) := by
  obtain ⟨sCap, hsCap⟩ :=
    pow_unbounded_of_one_lt (L / cfg.initialScale) (by norm_num : (1 : ℝ) < 2)
  have hscaleCap : L < cfg.scaleAt sCap := by
    rw [ControllerConfig.scaleAt]
    exact (div_lt_iff₀ hM).mp hsCap
  obtain ⟨rCap, hrCap⟩ := pow_unbounded_of_one_lt
    (R * cfg.scaleAt sCap / cfg.gradientSizeAtStart) (by norm_num : (1 : ℝ) < 2)
  refine ⟨{
    scaleCap := sCap
    radiusCap := rCap
    scaleDominates := ?_
    radiusDominates := ?_ }⟩
  · intro s hss
    have hp : (2 : ℝ) ^ sCap ≤ (2 : ℝ) ^ s :=
      pow_le_pow_right₀ (by norm_num) hss
    have hm : cfg.scaleAt sCap ≤ cfg.scaleAt s := by
      simpa [ControllerConfig.scaleAt] using
        (mul_le_mul_of_nonneg_right hp hM.le)
    exact hscaleCap.le.trans hm
  · intro s j hss hjj
    have hpScale : (2 : ℝ) ^ s ≤ (2 : ℝ) ^ sCap :=
      pow_le_pow_right₀ (by norm_num) hss
    have hscale : cfg.scaleAt s ≤ cfg.scaleAt sCap := by
      simpa [ControllerConfig.scaleAt] using
        (mul_le_mul_of_nonneg_right hpScale hM.le)
    have hscalePos : 0 < cfg.scaleAt s := by
      exact mul_pos (pow_pos (by norm_num) _) hM
    have hpowRadius : (2 : ℝ) ^ rCap ≤ (2 : ℝ) ^ j :=
      pow_le_pow_right₀ (by norm_num) hjj
    have hleft : R * cfg.scaleAt s ≤ R * cfg.scaleAt sCap :=
      mul_le_mul_of_nonneg_left hscale hR
    have hmiddle : R * cfg.scaleAt sCap < (2 : ℝ) ^ rCap * cfg.gradientSizeAtStart :=
      (div_lt_iff₀ hG).mp hrCap
    have hright : (2 : ℝ) ^ rCap * cfg.gradientSizeAtStart ≤
        (2 : ℝ) ^ j * cfg.gradientSizeAtStart :=
      mul_le_mul_of_nonneg_right hpowRadius hG.le
    rw [ControllerConfig.radiusAt, le_div_iff₀ hscalePos]
    exact hleft.trans (hmiddle.le.trans hright)

/-- Lexicographic search rank inside the finite cap rectangle. -/
def controllerRank {cfg : ControllerConfig} {L R : ℝ}
    (caps : ControllerCaps cfg L R)
    (state : ControllerState d) : ℕ :=
  (caps.scaleCap - state.scaleEpoch) * (caps.radiusCap + 1) +
    (caps.radiusCap - state.radiusLevel)

theorem controllerNext_rank_lt
    (oracle : PairOracle d) (gradientSize : Vec d → ℝ)
    (routine : TrialRoutine d) (cfg : ControllerConfig) (L R : ℝ)
    (caps : ControllerCaps cfg L R)
    {state state' : ControllerState d}
    (hs : state.scaleEpoch ≤ caps.scaleCap)
    (hj : state.radiusLevel ≤ caps.radiusCap)
    (hvalid : TrialValid oracle gradientSize cfg.eps L R
      (state.scale cfg) (state.radius cfg) (currentTrial routine cfg state))
    (hnext : ControllerNext routine cfg state' state) :
    controllerRank caps state' < controllerRank caps state := by
  unfold ControllerNext at hnext
  unfold currentTrial at hvalid hnext
  generalize hr : routine (state.scale cfg) (state.radius cfg) = report at hvalid hnext
  rcases state with ⟨s, j, total, rejected, history⟩
  simp only [ControllerState.scale, ControllerState.radius] at hvalid
  cases hout : report.outcome with
  | success x => simp [controllerStep, hout] at hnext
  | scale kind =>
      have hML : cfg.scaleAt s < L := by
        simpa [TrialValid, hout] using hvalid.2.2
      have hslt : s < caps.scaleCap := by
        by_contra hnot
        have hcaps : caps.scaleCap ≤ s := Nat.le_of_not_gt hnot
        exact (not_lt_of_ge (caps.scaleDominates s hcaps)) hML
      simp only [controllerStep, hout, ControllerStep.next.injEq] at hnext
      subst state'
      have hsub : caps.scaleCap - s = caps.scaleCap - (s + 1) + 1 := by omega
      simp only [controllerRank]
      rw [hsub, Nat.add_mul]
      omega
  | radius x =>
      have hDR : cfg.radiusAt s j < R := by
        have hsem := hvalid.2.2
        rw [hout] at hsem
        exact hsem.2
      have hjlt : j < caps.radiusCap := by
        by_contra hnot
        have hcaps : caps.radiusCap ≤ j := Nat.le_of_not_gt hnot
        exact (not_lt_of_ge (caps.radiusDominates s j hs hcaps)) hDR
      simp only [controllerStep, hout, ControllerStep.next.injEq] at hnext
      subst state'
      have hsub : caps.radiusCap - j = caps.radiusCap - (j + 1) + 1 := by omega
      simp only [controllerRank]
      rw [hsub]
      omega

theorem controllerNext_wellFounded
    (oracle : PairOracle d) (gradientSize : Vec d → ℝ)
    (routine : TrialRoutine d) (cfg : ControllerConfig) (L R : ℝ)
    (caps : ControllerCaps cfg L R)
    (hvalid : ∀ state,
      state.scaleEpoch ≤ caps.scaleCap →
      state.radiusLevel ≤ caps.radiusCap →
      TrialValid oracle gradientSize cfg.eps L R
        (state.scale cfg) (state.radius cfg) (currentTrial routine cfg state)) :
    WellFounded (fun state' state : ControllerState d =>
      state.scaleEpoch ≤ caps.scaleCap ∧
      state.radiusLevel ≤ caps.radiusCap ∧
      ControllerNext routine cfg state' state) := by
  apply Subrelation.wf ?_ (measure (controllerRank caps)).wf
  intro state' state h
  exact controllerNext_rank_lt oracle gradientSize routine cfg L R caps
    h.1 h.2.1 (hvalid state h.1 h.2.1) h.2.2

/-- A successful finish points to an actually queried terminal observation. -/
theorem controllerStep_done_queried
    {oracle : PairOracle d} {gradientSize : Vec d → ℝ} {L R : ℝ}
    {cfg : ControllerConfig} {state : ControllerState d}
    {report : TrialReport d} {finish : ControllerFinish d}
    (hvalid : TrialValid oracle gradientSize cfg.eps L R
      (state.scale cfg) (state.radius cfg) report)
    (hdone : controllerStep cfg state report = .done finish) :
    WasQueried report.observations finish.point ∧
      gradientSize (oracle.gradient finish.point) ≤ cfg.eps := by
  cases hout : report.outcome with
  | success x =>
      simp only [controllerStep, hout, ControllerStep.done.injEq] at hdone
      subst finish
      exact ⟨by simpa [TrialReport.OutcomeRecorded, hout] using hvalid.2.1,
        by simpa [TrialValid, hout] using hvalid.2.2⟩
  | scale kind => simp [controllerStep, hout] at hdone
  | radius x => simp [controllerStep, hout] at hdone

/--
Native formal counterpart of the frozen guarded-controller lemma at the
algorithm-semantics layer.  It proves termination from the two finite geometric
search caps, returns only a queried successful point, and proves the exact
prefix/rejected/terminal call decomposition.  Regime modules discharge
`TrialValid` and the numerical cap hypotheses.
-/
theorem guardedControllerWithCaps
    (oracle : PairOracle d) (gradientSize : Vec d → ℝ)
    (routine : TrialRoutine d) (cfg : ControllerConfig) (L R : ℝ)
    (caps : ControllerCaps cfg L R)
    (hvalid : ∀ state,
      state.scaleEpoch ≤ caps.scaleCap →
      state.radiusLevel ≤ caps.radiusCap →
      TrialValid oracle gradientSize cfg.eps L R
        (state.scale cfg) (state.radius cfg) (currentTrial routine cfg state)) :
    ∃ fuel finish,
      runController routine cfg fuel (initialControllerState cfg) = .success finish ∧
      finish.Accounting cfg ∧
      finish.HistoryAccounting cfg ∧
      ∃ terminalReport ∈ finish.history,
        WasQueried terminalReport.observations finish.point ∧
        gradientSize (oracle.gradient finish.point) ≤ cfg.eps := by
  let Rel := fun state' state : ControllerState d =>
    state.scaleEpoch ≤ caps.scaleCap ∧
    state.radiusLevel ≤ caps.radiusCap ∧
    ControllerNext routine cfg state' state
  have hwf : WellFounded Rel :=
    controllerNext_wellFounded oracle gradientSize routine cfg L R caps hvalid
  have hterminate : ∀ state : ControllerState d,
      state.scaleEpoch ≤ caps.scaleCap →
      state.radiusLevel ≤ caps.radiusCap →
      ∃ fuel finish,
        runController routine cfg fuel state = .success finish ∧
        ∃ terminalReport ∈ finish.history,
          WasQueried terminalReport.observations finish.point ∧
          gradientSize (oracle.gradient finish.point) ≤ cfg.eps := by
    intro state
    induction state using hwf.induction with
    | h state ih =>
        intro hs hj
        let report := currentTrial routine cfg state
        have hv := hvalid state hs hj
        cases hstep : controllerStep cfg state report with
        | done finish =>
            have hmem : report ∈ finish.history := by
              cases hout : report.outcome with
              | success x =>
                  simp [controllerStep, hout] at hstep
                  subst finish
                  simp
              | scale kind => simp [controllerStep, hout] at hstep
              | radius x => simp [controllerStep, hout] at hstep
            refine ⟨1, finish, ?_, report, hmem, ?_⟩
            · simp [runController, report, hstep]
            · exact controllerStep_done_queried hv hstep
        | next state' =>
            have hrel : Rel state' state := by
              refine ⟨hs, hj, ?_⟩
              simpa [ControllerNext, report] using hstep
            have hs' : state'.scaleEpoch ≤ caps.scaleCap := by
              unfold report at hstep
              generalize hh : currentTrial routine cfg state = r at hv hstep
              cases hout : r.outcome with
              | success x => simp [controllerStep, hout] at hstep
              | scale kind =>
                  have hML : state.scale cfg < L := by
                    simpa [TrialValid, hout] using hv.2.2
                  have hslt : state.scaleEpoch < caps.scaleCap := by
                    by_contra hnot
                    exact (not_lt_of_ge (caps.scaleDominates state.scaleEpoch
                      (Nat.le_of_not_gt hnot))) hML
                  simp [controllerStep, hout] at hstep
                  subst state'
                  simpa using (Nat.succ_le_iff.mpr hslt)
              | radius x =>
                  simp only [controllerStep, hout, ControllerStep.next.injEq] at hstep
                  subst state'
                  exact hs
            have hj' : state'.radiusLevel ≤ caps.radiusCap := by
              unfold report at hstep
              generalize hh : currentTrial routine cfg state = r at hv hstep
              cases hout : r.outcome with
              | success x => simp [controllerStep, hout] at hstep
              | scale kind =>
                  simp only [controllerStep, hout, ControllerStep.next.injEq] at hstep
                  subst state'
                  exact Nat.zero_le _
              | radius x =>
                  have hsem := hv.2.2
                  rw [hout] at hsem
                  have hDR : state.radius cfg < R := hsem.2
                  have hjlt : state.radiusLevel < caps.radiusCap := by
                    by_contra hnot
                    exact (not_lt_of_ge (caps.radiusDominates state.scaleEpoch
                      state.radiusLevel hs (Nat.le_of_not_gt hnot))) hDR
                  simp [controllerStep, hout] at hstep
                  subst state'
                  simpa using (Nat.succ_le_iff.mpr hjlt)
            obtain ⟨fuel, finish, hrun, terminalReport, hmem, hgood⟩ :=
              ih state' hrel hs' hj'
            refine ⟨fuel + 1, finish, ?_, terminalReport, hmem, hgood⟩
            simp [runController, report, hstep, hrun]
  obtain ⟨fuel, finish, hrun, terminalReport, hmem, hgood⟩ :=
    hterminate (initialControllerState cfg) (by simp [initialControllerState])
      (by simp [initialControllerState])
  refine ⟨fuel, finish, hrun, ?_, ?_, terminalReport, hmem, hgood⟩
  · have hacc := runController_accounting routine cfg
      (fuel := fuel) (state := initialControllerState cfg)
      (initialControllerState_accounting cfg (d := d))
    simpa [hrun] using hacc
  have hhist := runController_historyAccounting routine cfg
    (fuel := fuel) (state := initialControllerState cfg)
    (initialControllerState_historyAccounting cfg (d := d))
  simpa [hrun] using hhist

/--
The guarded controller with its finite geometric caps derived internally from
the positive scales.  Thus neither termination nor a successful trace is a
public input.
-/
theorem guardedControllerCore
    (oracle : PairOracle d) (gradientSize : Vec d → ℝ)
    (routine : TrialRoutine d) (cfg : ControllerConfig) (L R : ℝ)
    (hM : 0 < cfg.initialScale) (hG : 0 < cfg.gradientSizeAtStart)
    (hR : 0 ≤ R)
    (hvalid : ∀ state,
      TrialValid oracle gradientSize cfg.eps L R
        (state.scale cfg) (state.radius cfg) (currentTrial routine cfg state)) :
    ∃ fuel finish,
      runController routine cfg fuel (initialControllerState cfg) = .success finish ∧
      finish.Accounting cfg ∧
      finish.HistoryAccounting cfg ∧
      ∃ terminalReport ∈ finish.history,
        WasQueried terminalReport.observations finish.point ∧
        gradientSize (oracle.gradient finish.point) ≤ cfg.eps := by
  obtain ⟨caps⟩ := exists_controllerCaps cfg L R hM hG hR
  exact guardedControllerWithCaps oracle gradientSize routine cfg L R caps
    (fun state _ _ ↦ hvalid state)

end O3

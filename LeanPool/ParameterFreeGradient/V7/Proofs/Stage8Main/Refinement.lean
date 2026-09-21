/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage8Main.Controller

namespace V7.Stage8Main

def reportsTrace (reports : List (TrialReport d)) : List (Observation d) :=
  reports.flatMap TrialReport.trace

@[simp] theorem reportsTrace_append_singleton
    (reports : List (TrialReport d)) (report : TrialReport d) :
    reportsTrace (reports ++ [report]) = reportsTrace reports ++ report.trace := by
  simp [reportsTrace]

theorem reportsTrace_length (reports : List (TrialReport d)) :
    (reportsTrace reports).length =
      (reports.map (fun report => report.calls)).sum := by
  induction reports with
  | nil => simp [reportsTrace]
  | cons report reports ih =>
      simp [reportsTrace, TrialReport.calls, ih]

theorem first_action_query_of_exec_nonempty (trial : LocalTrial d)
    (oracle : PairOracle d) (M D : ℝ) (cached : CachedPair d)
    (report : TrialReport d) (hexec : trial.Executes M D cached oracle report)
    (hne : report.trace ≠ []) :
    ∃ x next, trial.action (trial.initial M D cached) = .query x next := by
  rcases hexec with ⟨fuel, hrun⟩
  cases fuel with
  | zero => simp [LocalTrial.runFuel] at hrun
  | succ fuel =>
      rw [LocalTrial.runFuel] at hrun
      cases haction : trial.action (trial.initial M D cached) with
      | query x next => exact ⟨x, next, rfl⟩
      | finish guards outcome =>
          simp [haction] at hrun
          have hempty : report.trace = [] := by rw [← hrun]
          exact (hne hempty).elim

theorem localTrial_run_to_done (oracle : PairOracle d)
    (data : RuntimeData d) (state : RuntimeControllerState d)
    (pre : List (Observation d)) :
    ∀ {localFuel : ℕ} {machineState : (runtimeTrial data state).State}
      {localHistory : List (Observation d)} {report : TrialReport d}
      {finish : RuntimeFinish d},
      (runtimeTrial data state).runFuel oracle localFuel machineState localHistory =
        some report →
      controllerStep data state report = .success finish →
      ∃ methodFuel,
        (currentMethod d).runFuel oracle methodFuel
          (.localTrial data state machineState localHistory)
          (pre ++ localHistory) =
        some (⟨finish.returned, pre ++ report.trace⟩ : O3.RunResult d) := by
  intro localFuel
  induction localFuel with
  | zero =>
      intro machineState localHistory report finish hrun
      simp [LocalTrial.runFuel] at hrun
  | succ localFuel ih =>
      intro machineState localHistory report finish hrun hstep
      let trial := runtimeTrial data state
      change trial.runFuel oracle (localFuel + 1) machineState localHistory =
        some report at hrun
      rw [LocalTrial.runFuel] at hrun
      cases haction : trial.action machineState with
      | finish guards outcome =>
          simp only [haction] at hrun
          injection hrun with hreport
          subst report
          cases hout : outcome with
          | success terminal =>
              refine ⟨1, ?_⟩
              simp [O3.FirstOrderMethod.runFuel, currentMethod, currentMethodAction,
                continueLocalAction, trial, haction, controllerStep, hout] at hstep ⊢
              cases hstep
              rfl
          | scale failed => simp [controllerStep, hout] at hstep
          | radius terminal => simp [controllerStep, hout] at hstep
      | query x next =>
          simp only [haction] at hrun
          let observation := oracle.observe x
          obtain ⟨methodFuel, hmethod⟩ := ih
            (machineState := next observation)
            (localHistory := localHistory ++ [observation])
            (report := report) (finish := finish) hrun hstep
          refine ⟨methodFuel + 1, ?_⟩
          dsimp only [currentMethod]
          rw [O3.FirstOrderMethod.runFuel]
          simp only [currentMethodAction, continueLocalAction, trial, haction]
          simpa [currentMethod, observation, List.append_assoc] using hmethod

theorem localTrial_run_to_next (oracle : PairOracle d)
    (data : RuntimeData d) (state state' : RuntimeControllerState d)
    (pre : List (Observation d)) {result : O3.RunResult d} {tailFuel : ℕ} :
    ∀ {localFuel : ℕ} {machineState : (runtimeTrial data state).State}
      {localHistory : List (Observation d)} {report : TrialReport d},
      (runtimeTrial data state).runFuel oracle localFuel machineState localHistory =
        some report →
      controllerStep data state report = .exhausted state' →
      (currentMethod d).runFuel oracle tailFuel (.controllerReady data state')
        (pre ++ report.trace) = some result →
      ∃ methodFuel,
        (currentMethod d).runFuel oracle methodFuel
          (.localTrial data state machineState localHistory)
          (pre ++ localHistory) = some result := by
  intro localFuel
  induction localFuel with
  | zero =>
      intro machineState localHistory report hrun
      simp [LocalTrial.runFuel] at hrun
  | succ localFuel ih =>
      intro machineState localHistory report hrun hstep htail
      let trial := runtimeTrial data state
      change trial.runFuel oracle (localFuel + 1) machineState localHistory =
        some report at hrun
      rw [LocalTrial.runFuel] at hrun
      cases haction : trial.action machineState with
      | finish guards outcome =>
          simp only [haction] at hrun
          injection hrun with hreport
          subst report
          cases tailFuel with
          | zero => simp [O3.FirstOrderMethod.runFuel] at htail
          | succ tailFuel =>
              refine ⟨tailFuel + 1, ?_⟩
              cases hout : outcome with
              | success terminal => simp [controllerStep, hout] at hstep
              | scale failed =>
                  simp [controllerStep, hout] at hstep
                  subst state'
                  simpa [currentMethod, currentMethodAction, continueLocalAction,
                    trial, haction, hout, O3.FirstOrderMethod.runFuel]
                    using htail
              | radius terminal =>
                  simp [controllerStep, hout] at hstep
                  subst state'
                  simpa [currentMethod, currentMethodAction, continueLocalAction,
                    trial, haction, hout, O3.FirstOrderMethod.runFuel]
                    using htail
      | query x next =>
          simp only [haction] at hrun
          let observation := oracle.observe x
          obtain ⟨methodFuel, hmethod⟩ := ih
            (machineState := next observation)
            (localHistory := localHistory ++ [observation])
            (report := report) hrun hstep htail
          refine ⟨methodFuel + 1, ?_⟩
          dsimp only [currentMethod]
          rw [O3.FirstOrderMethod.runFuel]
          simp only [currentMethodAction, continueLocalAction, trial, haction]
          change (currentMethod d).runFuel oracle methodFuel
            (.localTrial data state (next observation)
              (localHistory ++ [observation]))
            ((pre ++ localHistory) ++ [observation]) = some result
          simpa [observation, List.append_assoc] using hmethod

theorem controllerReady_run_to_done (data : RuntimeData d)
    (state : RuntimeControllerState d)
    (pre : List (Observation d))
    (inst : PositiveInstance data.input.p d data.input.x0)
    {spec : LocalRunSpec data state inst}
    {finish : RuntimeFinish d}
    (hstep : controllerStep data state spec.report = .success finish) :
    ∃ methodFuel,
      (currentMethod d).runFuel inst.oracle methodFuel (.controllerReady data state) pre =
        some { returned := finish.returned, queries := pre ++ spec.report.trace } := by
  rcases spec.executes with ⟨localFuel, hlocal⟩
  obtain ⟨x, next, hquery⟩ := first_action_query_of_exec_nonempty
    (runtimeTrial data state) inst.oracle (state.M data) (state.D data) data.cached
    spec.report ⟨localFuel, hlocal⟩ spec.trace_nonempty
  have hquery' :
      (runtimeTrial data state).action
        ((runtimeTrial data state).initial
          ((controllerConfig data).scaleAt state.scaleEpoch)
          ((controllerConfig data).radiusAt state.scaleEpoch state.radiusLevel)
          data.cached) = .query x next := by
    simpa using hquery
  obtain ⟨methodFuel, hmethod⟩ := localTrial_run_to_done inst.oracle data state pre
    (machineState := (runtimeTrial data state).initial
      (state.M data) (state.D data) data.cached)
    (localHistory := []) (report := spec.report) (finish := finish)
    hlocal hstep
  cases methodFuel with
  | zero => simp [O3.FirstOrderMethod.runFuel] at hmethod
  | succ methodFuel =>
      refine ⟨methodFuel + 1, ?_⟩
      simpa [O3.FirstOrderMethod.runFuel, currentMethod, currentMethodAction,
        startLocalAction, continueLocalAction, hquery'] using hmethod

theorem controllerReady_run_to_next (data : RuntimeData d)
    (state state' : RuntimeControllerState d)
    (pre : List (Observation d))
    (inst : PositiveInstance data.input.p d data.input.x0)
    {spec : LocalRunSpec data state inst}
    {result : O3.RunResult d} {tailFuel : ℕ}
    (hstep : controllerStep data state spec.report = .exhausted state')
    (htail : (currentMethod d).runFuel inst.oracle tailFuel (.controllerReady data state')
      (pre ++ spec.report.trace) = some result) :
    ∃ methodFuel,
      (currentMethod d).runFuel inst.oracle methodFuel (.controllerReady data state) pre =
        some result := by
  rcases spec.executes with ⟨localFuel, hlocal⟩
  obtain ⟨x, next, hquery⟩ := first_action_query_of_exec_nonempty
    (runtimeTrial data state) inst.oracle (state.M data) (state.D data) data.cached
    spec.report ⟨localFuel, hlocal⟩ spec.trace_nonempty
  have hquery' :
      (runtimeTrial data state).action
        ((runtimeTrial data state).initial
          ((controllerConfig data).scaleAt state.scaleEpoch)
          ((controllerConfig data).radiusAt state.scaleEpoch state.radiusLevel)
          data.cached) = .query x next := by
    simpa using hquery
  obtain ⟨methodFuel, hmethod⟩ := localTrial_run_to_next inst.oracle data state state'
    pre (machineState := (runtimeTrial data state).initial
      (state.M data) (state.D data) data.cached)
    (localHistory := []) (report := spec.report)
    hlocal hstep htail
  cases methodFuel with
  | zero => simp [O3.FirstOrderMethod.runFuel] at hmethod
  | succ methodFuel =>
      refine ⟨methodFuel + 1, ?_⟩
      simpa [O3.FirstOrderMethod.runFuel, currentMethod, currentMethodAction,
        startLocalAction, continueLocalAction, hquery'] using hmethod

theorem causalController_refines (data : RuntimeData d)
    (inst : PositiveInstance data.input.p d data.input.x0)
    (hcached : data.cached.observation = inst.oracle.observe data.input.x0)
    (hlarge : data.input.eps < lpNorm (conjugateExponent data.input.p)
      (inst.oracle.gradient data.input.x0))
    (publicPrefix : List (Observation d)) :
    ∀ {controllerFuel : ℕ} {state : RuntimeControllerState d}
      {finish : RuntimeFinish d},
      runController data inst hcached hlarge controllerFuel state = .success finish →
      ∃ methodFuel,
        (currentMethod d).runFuel inst.oracle methodFuel (.controllerReady data state)
          (publicPrefix ++ reportsTrace state.reports) =
        some (⟨finish.returned,
          publicPrefix ++ reportsTrace finish.reports⟩ : O3.RunResult d) := by
  intro controllerFuel
  induction controllerFuel with
  | zero =>
      intro state finish hrun
      simp [runController] at hrun
  | succ controllerFuel ih =>
      intro state finish hrun
      let spec := controllerLocalSpec data state inst hcached hlarge
      have hreport : controllerReport data inst hcached hlarge state = spec.report := rfl
      rw [runController, hreport] at hrun
      cases hstep : controllerStep data state spec.report with
      | success finish' =>
          rw [hstep] at hrun
          injection hrun with hfinish
          subst finish'
          obtain ⟨methodFuel, hmethod⟩ := controllerReady_run_to_done
            data state (publicPrefix ++ reportsTrace state.reports)
            inst (spec := spec) hstep
          refine ⟨methodFuel, ?_⟩
          cases hout : spec.report.outcome with
          | success terminal =>
              simp [controllerStep, hout] at hstep
              subst finish
              simpa [reportsTrace, List.append_assoc] using hmethod
          | scale failed => simp [controllerStep, hout] at hstep
          | radius terminal => simp [controllerStep, hout] at hstep
      | exhausted state' =>
          rw [hstep] at hrun
          obtain ⟨tailFuel, htail⟩ := ih hrun
          have htail' :
              (currentMethod d).runFuel inst.oracle tailFuel
                (.controllerReady data state')
                ((publicPrefix ++ reportsTrace state.reports) ++ spec.report.trace) =
              some (⟨finish.returned,
                publicPrefix ++ reportsTrace finish.reports⟩ : O3.RunResult d) := by
            cases hout : spec.report.outcome with
            | success terminal => simp [controllerStep, hout] at hstep
            | scale failed =>
                simp [controllerStep, hout] at hstep
                subst state'
                simpa [nextScale, List.append_assoc] using htail
            | radius terminal =>
                simp [controllerStep, hout] at hstep
                subst state'
                simpa [nextRadius, List.append_assoc] using htail
          exact controllerReady_run_to_next data state state'
            (publicPrefix ++ reportsTrace state.reports) inst (spec := spec) hstep htail'

end V7.Stage8Main

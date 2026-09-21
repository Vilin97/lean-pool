/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage8Main.AnchorSplice
import LeanPool.ParameterFreeGradient.V7.Proofs.Stage2Resume.Amortization

namespace V7.Stage8Main

def VisitTransition (G : ℝ) (current next : ControllerVisit)
    (report : TrialReport d) : Prop :=
  match report.outcome with
  | .success _ => False
  | .radius _ => next.M = current.M ∧ next.D = 2 * current.D
  | .scale _ => next.M = 2 * current.M ∧ next.D = G / next.M

private theorem at_append_of_lt {α : Type} (xs : List α) (x : α)
    {i : ℕ} (hi : i < xs.length) : (xs ++ [x])[i]? = xs[i]? := by
  simp [List.getElem?_append, hi]

private theorem at_append_boundary {α : Type} (xs : List α) (x : α) :
    (xs ++ [x])[xs.length]? = some x := by simp

theorem controllerPath_append (G Ma Da : ℝ)
    {visits : List ControllerVisit} {reports : List (TrialReport d)}
    (hpath : ControllerPath G Ma Da visits reports)
    (newVisit : ControllerVisit) (newReport : TrialReport d)
    (hlast : ∀ current report,
      VisitAt visits (visits.length - 1) current →
      ReportAt reports (reports.length - 1) report →
      VisitTransition G current newVisit report) :
    ControllerPath G Ma Da (visits ++ [newVisit]) (reports ++ [newReport]) := by
  have hn : 0 < visits.length := by
    by_contra h
    have hvnil : visits = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_not_pos h)
    simpa [hvnil] using hpath.2.1
  refine ⟨by simp [hpath.1], ?_, ?_⟩
  · cases visits with
    | nil => simp at hn
    | cons visit visits => simpa using hpath.2.1
  · intro i current next report hi hcurrent hnext hreport
    have hiBound : i + 1 ≤ visits.length := by simpa using hi
    by_cases hstrict : i + 1 < visits.length
    · apply hpath.2.2 i current next report hstrict
      · unfold VisitAt at hcurrent ⊢
        rw [List.head?_drop] at hcurrent ⊢
        rw [at_append_of_lt visits newVisit (by omega : i < visits.length)] at hcurrent
        exact hcurrent
      · unfold VisitAt at hnext ⊢
        rw [List.head?_drop] at hnext ⊢
        rw [at_append_of_lt visits newVisit hstrict] at hnext
        exact hnext
      · unfold ReportAt at hreport ⊢
        rw [List.head?_drop] at hreport ⊢
        have hiReports : i < reports.length := by rw [← hpath.1]; omega
        rw [at_append_of_lt reports newReport hiReports] at hreport
        exact hreport
    · have heq : i + 1 = visits.length := by omega
      have hiEq : i = visits.length - 1 := by omega
      have hrEq : i = reports.length - 1 := by rw [← hpath.1]; omega
      have hcOld : VisitAt visits (visits.length - 1) current := by
        unfold VisitAt at hcurrent ⊢
        rw [List.head?_drop] at hcurrent ⊢
        rw [at_append_of_lt visits newVisit (by omega : i < visits.length)] at hcurrent
        simpa [hiEq] using hcurrent
      have hrOld : ReportAt reports (reports.length - 1) report := by
        unfold ReportAt at hreport ⊢
        rw [List.head?_drop] at hreport ⊢
        have hiReports : i < reports.length := by rw [← hpath.1]; omega
        rw [at_append_of_lt reports newReport hiReports] at hreport
        simpa [hrEq] using hreport
      have hnxt : next = newVisit := by
        unfold VisitAt at hnext
        rw [List.head?_drop, heq, at_append_boundary] at hnext
        exact Option.some.inj hnext.symm
      subst next
      exact hlast current report hcOld hrOld

def ValidReport (data : RuntimeData d)
    (inst : PositiveInstance data.input.p d data.input.x0)
    (visit : ControllerVisit) (report : TrialReport d) : Prop :=
  GuardLedgerComplete data.input.p report report.checkedGuards ∧
  visit.D ≥ data.G / visit.M ∧
  TrialCertificate data.input.eps data.input.p visit.M visit.D
    inst.L inst.R data.cached inst.oracle report ∧
  (report.calls : ℝ) ≤ runtimeCoefficient data *
    (visit.M * visit.D / data.input.eps) ^ localCostExponent data.input.p

theorem validReport_of_spec (data : RuntimeData d)
    (state : RuntimeControllerState d)
    (inst : PositiveInstance data.input.p d data.input.x0)
    (spec : LocalRunSpec data state inst) :
    ValidReport data inst ⟨state.M data, state.D data⟩ spec.report := by
  exact ⟨spec.complete, state.D_ge_base data, spec.certificate, spec.calls_bound⟩

private theorem forall₂_append_singleton {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys)
    {x : α} {y : β} (hxy : R x y) :
    List.Forall₂ R (xs ++ [x]) (ys ++ [y]) := by
  induction h with
  | nil => exact .cons hxy .nil
  | cons hab htail ih => exact .cons hab ih

structure ReadyInvariant (data : RuntimeData d)
    (inst : PositiveInstance data.input.p d data.input.x0)
    (state : RuntimeControllerState d) : Prop where
  valid : List.Forall₂ (ValidReport data inst) state.visits state.reports
  pathWithNext : ∀ report,
    ControllerPath data.G data.Ma (data.G / data.Ma)
      (state.visits ++ [⟨state.M data, state.D data⟩])
      (state.reports ++ [report])

theorem initial_readyInvariant (data : RuntimeData d)
    (inst : PositiveInstance data.input.p d data.input.x0) :
    ReadyInvariant data inst initialRuntimeControllerState := by
  refine ⟨.nil, ?_⟩
  intro report
  refine ⟨by simp [initialRuntimeControllerState],
    by simp [initialRuntimeControllerState, RuntimeControllerState.M,
      RuntimeControllerState.D, controllerConfig], ?_⟩
  intro i current next prior hi
  simp [initialRuntimeControllerState] at hi

theorem readyInvariant_nextScale (data : RuntimeData d)
    (inst : PositiveInstance data.input.p d data.input.x0)
    (state : RuntimeControllerState d) (spec : LocalRunSpec data state inst)
    (failed : ObservableGuardCheck d) (hout : spec.report.outcome = .scale failed)
    (hinv : ReadyInvariant data inst state) :
    ReadyInvariant data inst (nextScale data state spec.report) := by
  refine ⟨?_, ?_⟩
  · exact forall₂_append_singleton hinv.valid (validReport_of_spec data state inst spec)
  · intro nextReport
    apply controllerPath_append data.G data.Ma (data.G / data.Ma)
      (hinv.pathWithNext spec.report)
    intro current report hcurrent hreport
    have hc : current = (⟨state.M data, state.D data⟩ : ControllerVisit) := by
      unfold VisitAt at hcurrent
      rw [List.head?_drop] at hcurrent
      simp at hcurrent
      exact hcurrent.symm
    have hr : report = spec.report := by
      unfold ReportAt at hreport
      rw [List.head?_drop] at hreport
      simp at hreport
      exact hreport.symm
    subst current
    subst report
    simp [VisitTransition, hout, nextScale, RuntimeControllerState.M,
      RuntimeControllerState.D, pow_succ]
    ring

theorem readyInvariant_nextRadius (data : RuntimeData d)
    (inst : PositiveInstance data.input.p d data.input.x0)
    (state : RuntimeControllerState d) (spec : LocalRunSpec data state inst)
    (terminal : Observation d) (hout : spec.report.outcome = .radius terminal)
    (hinv : ReadyInvariant data inst state) :
    ReadyInvariant data inst (nextRadius data state spec.report) := by
  refine ⟨?_, ?_⟩
  · exact forall₂_append_singleton hinv.valid (validReport_of_spec data state inst spec)
  · intro nextReport
    apply controllerPath_append data.G data.Ma (data.G / data.Ma)
      (hinv.pathWithNext spec.report)
    intro current report hcurrent hreport
    have hc : current = (⟨state.M data, state.D data⟩ : ControllerVisit) := by
      unfold VisitAt at hcurrent
      rw [List.head?_drop] at hcurrent
      simp at hcurrent
      exact hcurrent.symm
    have hr : report = spec.report := by
      unfold ReportAt at hreport
      rw [List.head?_drop] at hreport
      simp at hreport
      exact hreport.symm
    subst current
    subst report
    simp [VisitTransition, hout, nextRadius, RuntimeControllerState.M,
      RuntimeControllerState.D, pow_succ]
    ring

structure FinishInvariant (data : RuntimeData d)
    (inst : PositiveInstance data.input.p d data.input.x0)
    (finish : RuntimeFinish d) : Prop where
  path : ControllerPath data.G data.Ma (data.G / data.Ma)
    finish.visits finish.reports
  valid : List.Forall₂ (ValidReport data inst) finish.visits finish.reports
  terminal : ∃ report terminal,
    report ∈ finish.reports ∧ report.outcome = .success terminal ∧
    terminal.point = finish.returned ∧ terminal ∈ report.trace ∧
    lpNorm (conjugateExponent data.input.p)
      (inst.oracle.gradient terminal.point) ≤ data.input.eps

theorem runController_invariant (data : RuntimeData d)
    (inst : PositiveInstance data.input.p d data.input.x0)
    (hcached : data.cached.observation = inst.oracle.observe data.input.x0)
    (hlarge : data.input.eps < lpNorm (conjugateExponent data.input.p)
      (inst.oracle.gradient data.input.x0)) :
    ∀ {fuel state finish},
      ReadyInvariant data inst state →
      runController data inst hcached hlarge fuel state = .success finish →
      FinishInvariant data inst finish := by
  intro fuel
  induction fuel with
  | zero =>
      intro state finish hinv hrun
      simp [runController] at hrun
  | succ fuel ih =>
      intro state finish hinv hrun
      let spec := controllerLocalSpec data state inst hcached hlarge
      have hreport : controllerReport data inst hcached hlarge state = spec.report := rfl
      rw [runController, hreport] at hrun
      cases hout : spec.report.outcome with
      | success terminal =>
          simp [controllerStep, hout] at hrun
          subst finish
          refine ⟨hinv.pathWithNext spec.report,
            forall₂_append_singleton hinv.valid
              (validReport_of_spec data state inst spec), ?_⟩
          refine ⟨spec.report, terminal, by simp, hout, rfl, ?_, ?_⟩
          · exact (spec.certificate.2.2.2.1 terminal hout).1
          · have hs := spec.certificate.2.2.2.1 terminal hout
            have hgrad := congrArg O3.Observation.gradient hs.2.1
            change terminal.gradient = inst.oracle.gradient terminal.point at hgrad
            rw [← hgrad]
            exact hs.2.2.2
      | scale failed =>
          simp [controllerStep, hout] at hrun
          exact ih (readyInvariant_nextScale data inst state spec failed hout hinv) hrun
      | radius terminal =>
          simp [controllerStep, hout] at hrun
          exact ih (readyInvariant_nextRadius data inst state spec terminal hout hinv) hrun

end V7.Stage8Main

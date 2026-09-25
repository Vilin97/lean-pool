/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.O3.Foundation

/-!
# Exact pair-oracle observations and guarded trial reports

This module contains data only: exact oracle observations, finite traces,
observable scalar guard checks, and the three possible trial outcomes.  In
particular, a `TrialReport` does not contain a proof of a target gradient
bound, a radius classification, or successful controller termination.
Those properties live in the separate proposition `TrialValid` and must be
proved by the regime-specific trial modules.
-/

@[expose] public section

namespace O3

/-- A finite, chronological list of counted pair-oracle observations. -/
abbrev OracleTrace (d : ℕ) := List (Observation d)

/-- Each observation in the trace is one counted pair-oracle call. -/
def oracleCallCount (trace : OracleTrace d) : ℕ := trace.length

/-- Every recorded observation is the exact answer returned at its point. -/
def TraceExact (oracle : PairOracle d) (trace : OracleTrace d) : Prop :=
  ∀ o ∈ trace, o = oracle.observe o.point

/-- A point was actually queried in the given trace. -/
def WasQueried (trace : OracleTrace d) (x : Vec d) : Prop :=
  ∃ o ∈ trace, o.point = x

theorem traceExact_nil (oracle : PairOracle d) :
    TraceExact oracle [] := by
  simp [TraceExact]

theorem traceExact_append {oracle : PairOracle d} {s t : OracleTrace d}
    (hs : TraceExact oracle s) (ht : TraceExact oracle t) :
    TraceExact oracle (s ++ t) := by
  intro o ho
  rcases List.mem_append.mp ho with ho | ho
  · exact hs o ho
  · exact ht o ho

theorem oracleCallCount_append (s t : OracleTrace d) :
    oracleCallCount (s ++ t) = oracleCallCount s + oracleCallCount t := by
  simp [oracleCallCount]

/-- The three oracle-checkable guard classes in the frozen TeX source. -/
inductive GuardKind where
  | upperModel
  | gradientLipschitz
  | interpolation
  deriving DecidableEq

/--
An observable guard is stored through its scalar margin.  The convention is
that the checked inequality passes exactly when `0 ≤ margin`.
-/
structure GuardCheck where
  /-- The analytic condition tested by this observable guard. -/
  kind : GuardKind
  /-- The signed slack of the tested inequality, with nonnegative values denoting success. -/
  margin : ℝ

/-- The guard's inequality holds exactly when its signed margin is nonnegative. -/
def GuardCheck.Holds (check : GuardCheck) : Prop := 0 ≤ check.margin

/-- Margin for `f(y) ≤ f(x) + linear + (M/2) * stepSq`. -/
noncomputable def upperModelGuard (fx fy linear stepSq M : ℝ) : GuardCheck :=
  { kind := .upperModel
    margin := fx + linear + (M / 2) * stepSq - fy }

/-- Margin for `gradDiff ≤ M * stepNorm`. -/
def gradientGuard (gradDiff stepNorm M : ℝ) : GuardCheck :=
  { kind := .gradientLipschitz
    margin := M * stepNorm - gradDiff }

/--
Margin for the ordered Euclidean finite-data interpolation guard
`f_i-f_j-pairing-(2M)^{-1} gradDiffSq ≥ 0`.
-/
noncomputable def interpolationGuard
    (fi fj pairing gradDiffSq M : ℝ) : GuardCheck :=
  { kind := .interpolation
    margin := fi - fj - pairing - gradDiffSq / (2 * M) }

theorem upperModelGuard_holds_iff (fx fy linear stepSq M : ℝ) :
    (upperModelGuard fx fy linear stepSq M).Holds ↔
      fy ≤ fx + linear + (M / 2) * stepSq := by
  simp [GuardCheck.Holds, upperModelGuard]

theorem gradientGuard_holds_iff (gradDiff stepNorm M : ℝ) :
    (gradientGuard gradDiff stepNorm M).Holds ↔
      gradDiff ≤ M * stepNorm := by
  simp [GuardCheck.Holds, gradientGuard]

theorem interpolationGuard_holds_iff (fi fj pairing gradDiffSq M : ℝ) :
    (interpolationGuard fi fj pairing gradDiffSq M).Holds ↔
      0 ≤ fi - fj - pairing - gradDiffSq / (2 * M) := by
  rfl

/-- Every guard recorded in the list has a nonnegative margin. -/
def allGuardsPass (guards : List GuardCheck) : Prop :=
  ∀ check ∈ guards, check.Holds

/-- The list contains a failed guard of the specified kind. -/
def HasFailedGuard (guards : List GuardCheck) (kind : GuardKind) : Prop :=
  ∃ check ∈ guards, check.kind = kind ∧ ¬ check.Holds

/-- Data-level outcome of a deterministic guarded local trial. -/
inductive TrialOutcome (d : ℕ) where
  | success (point : Vec d)
  | scale (failedKind : GuardKind)
  | radius (finalPoint : Vec d)

/--
Finite data emitted by a local trial.  `calls` is deliberately not a free
field: it is the length of the exact observation trace.
-/
structure TrialReport (d : ℕ) where
  /-- The chronological oracle responses obtained during the local trial. -/
  observations : OracleTrace d
  /-- The observable inequality checks performed by the local trial. -/
  guards : List GuardCheck
  /-- The trial's success or rejection outcome. -/
  outcome : TrialOutcome d

/-- The number of counted pair-oracle calls in the trial report. -/
def TrialReport.calls (report : TrialReport d) : ℕ :=
  oracleCallCount report.observations

/--
One action of an explicit interactive local trial.  Only `query` can obtain new
objective data.  `finish` records observable guards and a data-level outcome.
-/
inductive TrialMachineAction (d : ℕ) (State : Type) where
  | query (point : Vec d) (next : Observation d → State)
  | finish (guards : List GuardCheck) (outcome : TrialOutcome d)

/-- A deterministic guarded-trial state-machine component, parameterized by `M,D`. -/
structure GuardedTrialMachine (d : ℕ) where
  /-- The internal states of the interactive guarded trial. -/
  State : Type
  /-- Initialize a local trial from its proposed scale and radius. -/
  initial : ℝ → ℝ → State
  /-- Select the next query or terminal report from a local-trial state. -/
  action : State → TrialMachineAction d State

/--
Fuel-bounded execution of a local trial.  The returned report contains exactly
the chronological calls performed by its `query` transitions.
-/
def GuardedTrialMachine.runFuel {d : ℕ} (machine : GuardedTrialMachine d)
    (oracle : PairOracle d) :
    ℕ → machine.State → OracleTrace d → Option (TrialReport d)
  | 0, _, _ => none
  | fuel + 1, state, history =>
      match machine.action state with
      | .finish guards outcome => some ⟨history, guards, outcome⟩
      | .query x next =>
          let obs := oracle.observe x
          machine.runFuel oracle fuel (next obs) (history ++ [obs])

/-- Execute the guarded trial from its initial state with the given scale, radius, and fuel. -/
def GuardedTrialMachine.run {d : ℕ} (machine : GuardedTrialMachine d)
    (oracle : PairOracle d) (M D : ℝ) (fuel : ℕ) : Option (TrialReport d) :=
  machine.runFuel oracle fuel (machine.initial M D) []

theorem GuardedTrialMachine.runFuel_traceExact {d : ℕ}
    (machine : GuardedTrialMachine d) (oracle : PairOracle d)
    {fuel : ℕ} {state : machine.State} {history : OracleTrace d}
    (hhistory : TraceExact oracle history) {report : TrialReport d}
    (hrun : machine.runFuel oracle fuel state history = some report) :
    TraceExact oracle report.observations := by
  induction fuel generalizing state history with
  | zero => simp [GuardedTrialMachine.runFuel] at hrun
  | succ fuel ih =>
      rw [GuardedTrialMachine.runFuel] at hrun
      cases haction : machine.action state with
      | finish guards outcome =>
          simp only [haction, Option.some.injEq] at hrun
          subst report
          exact hhistory
      | query x next =>
          simp only [haction] at hrun
          apply ih (traceExact_append hhistory ?_) hrun
          intro o ho
          simp at ho
          subst o
          rfl

theorem GuardedTrialMachine.run_traceExact {d : ℕ}
    (machine : GuardedTrialMachine d) (oracle : PairOracle d)
    {M D : ℝ} {fuel : ℕ} {report : TrialReport d}
    (hrun : machine.run oracle M D fuel = some report) :
    TraceExact oracle report.observations := by
  exact machine.runFuel_traceExact oracle (traceExact_nil oracle) hrun

/-- Purely data-level consistency of the recorded outcome. -/
def TrialReport.OutcomeRecorded (report : TrialReport d) : Prop :=
  match report.outcome with
  | .success x => WasQueried report.observations x
  | .scale kind => HasFailedGuard report.guards kind
  | .radius x => WasQueried report.observations x ∧ allGuardsPass report.guards

/--
Semantic obligations proved by a regime-specific local trial.  This is a
proposition, not a certificate field.  The scale and radius conclusions are
exactly the directional implications used by the frozen outer-controller
lemma.
-/
def TrialValid
    (oracle : PairOracle d) (gradientSize : Vec d → ℝ)
    (eps L R M D : ℝ) (report : TrialReport d) : Prop :=
  TraceExact oracle report.observations ∧
  report.OutcomeRecorded ∧
  match report.outcome with
  | .success x => gradientSize (oracle.gradient x) ≤ eps
  | .scale _ => M < L
  | .radius x => eps < gradientSize (oracle.gradient x) ∧ D < R

theorem TrialValid.traceExact {oracle : PairOracle d} {gradientSize : Vec d → ℝ}
    {eps L R M D : ℝ} {report : TrialReport d}
    (h : TrialValid oracle gradientSize eps L R M D report) :
    TraceExact oracle report.observations := h.1

theorem TrialValid.outcomeRecorded {oracle : PairOracle d} {gradientSize : Vec d → ℝ}
    {eps L R M D : ℝ} {report : TrialReport d}
    (h : TrialValid oracle gradientSize eps L R M D report) :
    report.OutcomeRecorded := h.2.1

end O3

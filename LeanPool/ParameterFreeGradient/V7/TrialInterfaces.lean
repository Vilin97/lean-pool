/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Guards

/-!
Causal local trial actions, observable reports, guard ledgers, and correctness certificates.
-/

@[expose] public section

namespace V7

/-- An observable guard kind together with the exact pairs used to evaluate it. -/
structure ObservableGuardCheck (d : ℕ) where
  /-- The observable inequality to be evaluated. -/
  kind : ObservableGuardKind
  /-- The observation at the guard's first point. -/
  xPair : Observation d
  /-- The observation at the guard's second point. -/
  yPair : Observation d

/-- The point-based failure witness associated with an observation-based guard check. -/
def ObservableGuardCheck.failure (check : ObservableGuardCheck d) : ObservableGuardFailure d :=
  ⟨check.kind, check.xPair.point, check.yPair.point⟩

/-- A trial terminates with gradient success, a failed scale guard, or an insufficient radius. -/
inductive TrialOutcome (d : ℕ) where
  | success (terminalPair : Observation d)
  | scale (failedCheck : ObservableGuardCheck d)
  | radius (terminalPair : Observation d)

/-- Observable data only: no `M<L` or `D<R` conclusion is stored here. -/
structure TrialReport (d : ℕ) where
  /-- The chronological new observations made by the trial. -/
  trace : List (Observation d)
  /-- The chronological observable guards checked by the trial. -/
  checkedGuards : List (ObservableGuardCheck d)
  /-- The terminal trial outcome and its observable witness. -/
  outcome : TrialOutcome d

/-- The number of new oracle observations recorded by the trial. -/
def TrialReport.calls (report : TrialReport d) : ℕ := report.trace.length

/-- An observation retained for reuse without another oracle call. -/
structure CachedPair (d : ℕ) where
  /-- The previously obtained exact value-gradient observation. -/
  observation : Observation d

/-- A local trial either requests an observation or finishes with guards and an outcome. -/
inductive LocalTrialAction (d : ℕ) (State : Type) where
  | query (point : Point d) (next : Observation d → State)
  | finish (guards : List (ObservableGuardCheck d)) (outcome : TrialOutcome d)

/-- A causal local trial: cached data enters the initial state, and all later
objective information enters only through `query` continuations. -/
structure LocalTrial (d : ℕ) where
  /-- The internal state type of the causal local trial. -/
  State : Type
  /-- The initial state determined by the trial estimates and cached observation. -/
  initial : ℝ → ℝ → CachedPair d → State
  /-- The next observable action determined by the current internal state. -/
  action : State → LocalTrialAction d State

/-- The finite-fuel local execution, returning no report if its action budget is exhausted. -/
def LocalTrial.runFuel (trial : LocalTrial d) (oracle : PairOracle d) :
    ℕ → trial.State → List (Observation d) → Option (TrialReport d)
  | 0, _, _ => none
  | fuel + 1, state, history =>
      match trial.action state with
      | .finish guards outcome => some ⟨history, guards, outcome⟩
      | .query x next =>
          let obs := oracle.observe x
          trial.runFuel oracle fuel (next obs) (history ++ [obs])

/-- Some finite-fuel execution from the prescribed initial state returns this report. -/
def LocalTrial.Executes (trial : LocalTrial d) (M D : ℝ) (cached : CachedPair d)
    (oracle : PairOracle d) (report : TrialReport d) : Prop :=
  ∃ fuel, trial.runFuel oracle fuel (trial.initial M D cached) [] = some report

/-- A success report returns an exact queried point meeting the gradient target after accepted
guards. -/
def SuccessCorrect (eps p M : ℝ) (oracle : PairOracle d)
    (report : TrialReport d) : Prop :=
  ∀ obs, report.outcome = .success obs →
    obs ∈ report.trace ∧ obs = oracle.observe obs.point ∧
      (∀ check ∈ report.checkedGuards,
        ¬ GuardFails p M oracle check.failure) ∧
      lpNorm (conjugateExponent p) obs.gradient ≤ eps

/-- A scale report identifies the first failed guard and certifies that the smoothness estimate is
too small. -/
def ScaleCorrect (p M L : ℝ) (oracle : PairOracle d)
    (report : TrialReport d) : Prop :=
  ∀ failed, report.outcome = .scale failed →
    failed ∈ report.checkedGuards ∧
      report.checkedGuards.getLast? = some failed ∧
      (∀ check ∈ report.checkedGuards.dropLast,
        ¬ GuardFails p M oracle check.failure) ∧
      GuardFails p M oracle failed.failure ∧ M < L

/-- A radius report has accepted guards and certifies that its radius estimate is too small. -/
def RadiusCorrect (eps p M D R : ℝ) (oracle : PairOracle d)
    (report : TrialReport d) : Prop :=
  ∀ terminal, report.outcome = .radius terminal →
    terminal ∈ report.trace ∧ terminal = oracle.observe terminal.point ∧
    (∀ check ∈ report.checkedGuards,
      ¬ GuardFails p M oracle check.failure) ∧
    eps < lpNorm (conjugateExponent p) terminal.gradient ∧ D < R

/-- The report belongs to one of the three possible terminal outcome cases. -/
def TrialOutcomeExhaustive (report : TrialReport d) : Prop :=
  (∃ x, report.outcome = .success x) ∨
  (∃ g, report.outcome = .scale g) ∨
  ∃ x, report.outcome = .radius x

/-- The numbers of consecutive guard checks and calls agree with the terminal outcome. -/
def TrialReport.consecutiveGuardAccounting (report : TrialReport d) : Prop :=
  match report.outcome with
  | .success _ => report.checkedGuards.length + 1 = report.calls
  | .scale _ => report.checkedGuards.length = report.calls
  | .radius _ => report.checkedGuards.length = report.calls

/-- The observation is either cached or present in the trial's new query trace. -/
def ObservationAvailable (cached : CachedPair d) (report : TrialReport d)
    (obs : Observation d) : Prop :=
  obs = cached.observation ∨ obs ∈ report.trace

/-- The guard's observations are consecutive in the cached observation followed by the trial
trace. -/
def ConsecutiveAvailable (cached : CachedPair d) (report : TrialReport d)
    (check : ObservableGuardCheck d) : Prop :=
  ∃ before after,
    cached.observation :: report.trace =
      before ++ [check.xPair, check.yPair] ++ after

/-- Every recorded guard has a kind in the allowed list. -/
def CheckedGuardsHaveKinds (report : TrialReport d)
    (allowed : List ObservableGuardKind) : Prop :=
  ∀ check ∈ report.checkedGuards, check.kind ∈ allowed

/-- A guard of the specified kind and ordered pair of points occurs in the checked list. -/
def GuardRecorded (report : TrialReport d) (kind : ObservableGuardKind)
    (x y : Point d) : Prop :=
  ∃ check ∈ report.checkedGuards,
    check.kind = kind ∧ check.xPair.point = x ∧ check.yPair.point = y

/-- Each guard uses the corresponding consecutive pair in the cached observation and query trace. -/
def ConsecutiveGuardLedger (cached : CachedPair d)
    (report : TrialReport d) : Prop :=
  ∀ i < report.checkedGuards.length, ∃ check,
    (report.checkedGuards.drop i).head? = some check ∧
    ((cached.observation :: report.trace).drop i).head? = some check.xPair ∧
    ((cached.observation :: report.trace).drop (i + 1)).head? = some check.yPair

/-- Every predicate reported by the routine is evaluated on exact pairs that
the routine actually possesses: the cached pair or a chronological query. -/
def GuardDataExact (cached : CachedPair d) (oracle : PairOracle d)
    (report : TrialReport d) : Prop :=
  cached.observation = oracle.observe cached.observation.point ∧
  ∀ check ∈ report.checkedGuards,
    ObservationAvailable cached report check.xPair ∧
    ObservationAvailable cached report check.yPair ∧
    check.xPair = oracle.observe check.xPair.point ∧
    check.yPair = oracle.observe check.yPair.point

/-- Correctness proposition kept separate from observable trial data. -/
def TrialCertificate (eps p M D L R : ℝ) (cached : CachedPair d)
    (oracle : PairOracle d)
    (report : TrialReport d) : Prop :=
  TraceExact oracle report.trace ∧
  GuardDataExact cached oracle report ∧
  TrialOutcomeExhaustive report ∧
  SuccessCorrect eps p M oracle report ∧
  ScaleCorrect p M L oracle report ∧
  RadiusCorrect eps p M D R oracle report

end V7

/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.TrialInterfaces

/-!
Finite Euclidean phase data, guard schedules, and the two-phase local trial contract.
-/

@[expose] public section

open scoped BigOperators

namespace V7

/-- Instance, coefficients, iterates, and observations of the Euclidean gap-reduction phase. -/
structure EuclideanGapData (d m : ℕ) where
  /-- The starting point of the Euclidean phase. -/
  x0 : Point d
  /-- The positive secant instance governing the objective and oracle. -/
  inst : PositiveInstance 2 d x0
  /-- The smoothness estimate used by the phase. -/
  M : ℝ
  /-- The radius estimate used to bound the initial distance to a minimizer. -/
  D : ℝ
  /-- The cumulative estimate-sequence weights. -/
  A : ℕ → ℝ
  /-- The increments of the estimate-sequence weights. -/
  a : ℕ → ℝ
  /-- The accelerated primal iterates. -/
  x : ℕ → Point d
  /-- The minimizers of the accumulated quadratic estimate potentials. -/
  w : ℕ → Point d
  /-- The interpolated oracle query points. -/
  y : ℕ → Point d
  /-- The chronological oracle observations of the Euclidean phase. -/
  trace : List (Observation d)

/-- The initial state, coefficient equations, and accelerated Euclidean update recurrences. -/
def EuclideanGapDynamics (data : EuclideanGapData d m) : Prop :=
  0 < data.M ∧ data.A 0 = 0 ∧ data.x 0 = data.x0 ∧ data.w 0 = data.x0 ∧
  ∀ k < m,
    0 < data.a (k + 1) ∧
    (data.a (k + 1)) ^ (2 : ℕ) = data.A k + data.a (k + 1) ∧
    data.A (k + 1) = data.A k + data.a (k + 1) ∧
    data.y k =
      (data.A k / data.A (k + 1)) • data.x k +
      (data.a (k + 1) / data.A (k + 1)) • data.w k ∧
    data.w (k + 1) = data.x0 - (1 / data.M) •
      (fun j => ∑ i ∈ Finset.range (k + 1),
        data.a (i + 1) * data.inst.oracle.gradient (data.y i) j) ∧
    data.x (k + 1) =
      (data.A k / data.A (k + 1)) • data.x k +
      (data.a (k + 1) / data.A (k + 1)) • data.w (k + 1)

/-- The Euclidean dynamics, radius bound, accepted models, and exact observation trace. -/
def EuclideanGapAssumptions (data : EuclideanGapData d m) : Prop :=
  EuclideanGapDynamics data ∧ data.inst.R ≤ data.D ∧
  data.x 0 = data.x0 ∧ data.w 0 = data.x0 ∧
  (∀ k < m,
    0 < data.a (k + 1) ∧
    (data.a (k + 1)) ^ (2 : ℕ) = data.A k + data.a (k + 1) ∧
    data.A (k + 1) = data.A k + data.a (k + 1) ∧
    data.y k =
      (data.A k / data.A (k + 1)) • data.x k +
      (data.a (k + 1) / data.A (k + 1)) • data.w k ∧
    data.w (k + 1) = data.x0 - (1 / data.M) •
      (fun j => ∑ i ∈ Finset.range (k + 1),
        data.a (i + 1) * data.inst.oracle.gradient (data.y i) j) ∧
    data.x (k + 1) =
      (data.A k / data.A (k + 1)) • data.x k +
      (data.a (k + 1) / data.A (k + 1)) • data.w (k + 1)) ∧
  TraceExact data.inst.oracle data.trace ∧
  data.trace = (List.range m).flatMap (fun k =>
    [data.inst.oracle.observe (data.y k),
      data.inst.oracle.observe (data.x (k + 1))]) ∧
  (∀ k < m,
    UpperModelGuard 2 data.M data.inst.oracle (data.y k) (data.x (k + 1))) ∧
  0 < data.A m

/-- Source carrier for `lem:euclideangap` (E01). -/
noncomputable def EuclideanGapStatement : Prop :=
  ∀ (d m : ℕ) (data : EuclideanGapData d m),
    EuclideanGapAssumptions data →
    data.inst.oracle.value (data.x m) - data.inst.fstar ≤
      data.M * data.D ^ (2 : ℕ) / (2 * data.A m) ∧
    data.M * data.D ^ (2 : ℕ) / (2 * data.A m) ≤
      2 * data.M * data.D ^ (2 : ℕ) / ((m : ℝ) + 1) ^ (2 : ℕ)

/-- Oracle, coefficients, iterates, and observations of a finite OGM-G execution. -/
structure OGMGData (d n : ℕ) where
  /-- The value-gradient oracle queried by OGM-G. -/
  oracle : PairOracle d
  /-- The smoothness estimate scaling the OGM-G gradient steps. -/
  M : ℝ
  /-- The proposed minimum objective value. -/
  fstar : ℝ
  /-- The starting point of the OGM-G phase. -/
  U : Point d
  /-- The backward momentum coefficient sequence. -/
  theta : ℕ → ℝ
  /-- The OGM-G query iterates. -/
  u : ℕ → Point d
  /-- The gradient-step points computed from the query iterates. -/
  v : ℕ → Point d
  /-- The previous gradient-step point before iteration zero. -/
  vMinusOne : Point d
  /-- The chronological oracle observations of the OGM-G phase. -/
  trace : List (Observation d)

/-- The backward coefficient equations, initial state, and literal OGM-G update recurrences. -/
def OGMGDynamics (data : OGMGData d n) : Prop :=
  1 ≤ n ∧ 0 < data.M ∧ data.theta n = 1 ∧
  data.u 0 = data.U ∧ data.vMinusOne = data.U ∧
  (∀ i, 1 ≤ i → i < n →
    data.theta i =
      (1 + Real.sqrt (1 + 4 * (data.theta (i + 1)) ^ (2 : ℕ))) / 2) ∧
  data.theta 0 =
    (1 + Real.sqrt (1 + 8 * (data.theta 1) ^ (2 : ℕ))) / 2 ∧
  (∀ i < n,
    data.v i = data.u i - (1 / data.M) • data.oracle.gradient (data.u i) ∧
    data.u (i + 1) = data.v i +
      (((data.theta i - 1) * (2 * data.theta (i + 1) - 1)) /
        (data.theta i * (2 * data.theta i - 1))) •
          (data.v i - (if i = 0 then data.vMinusOne else data.v (i - 1))) +
      ((2 * data.theta (i + 1) - 1) / (2 * data.theta i - 1)) •
        (data.v i - data.u i)) ∧
  data.v n = data.u n - (1 / data.M) • data.oracle.gradient (data.u n)

/-- The OGM-G dynamics, convex gradient oracle, attained minimum, guards, and exact trace. -/
def OGMGAssumptions (data : OGMGData d n) : Prop :=
  OGMGDynamics data ∧ O3.IsConvexObjective data.oracle.value ∧
  O3.IsCoordinateGradient data.oracle.value data.oracle.gradient ∧
  data.fstar = sInf (Set.range data.oracle.value) ∧
  (∃ xstar, data.oracle.value xstar = data.fstar ∧
    ∀ x, data.oracle.value xstar ≤ data.oracle.value x) ∧
  data.theta n = 1 ∧ data.u 0 = data.U ∧ data.vMinusOne = data.U ∧
  (∀ i, 1 ≤ i → i < n →
    data.theta i =
      (1 + Real.sqrt (1 + 4 * (data.theta (i + 1)) ^ (2 : ℕ))) / 2) ∧
  data.theta 0 =
    (1 + Real.sqrt (1 + 8 * (data.theta 1) ^ (2 : ℕ))) / 2 ∧
  (∀ i < n,
    data.v i = data.u i - (1 / data.M) • data.oracle.gradient (data.u i) ∧
    data.u (i + 1) = data.v i +
      (((data.theta i - 1) * (2 * data.theta (i + 1) - 1)) /
        (data.theta i * (2 * data.theta i - 1))) •
          (data.v i - (if i = 0 then data.vMinusOne else data.v (i - 1))) +
      ((2 * data.theta (i + 1) - 1) / (2 * data.theta i - 1)) •
        (data.v i - data.u i)) ∧
  data.v n = data.u n - (1 / data.M) • data.oracle.gradient (data.u n) ∧
  TraceExact data.oracle data.trace ∧
  data.trace = ((List.range (n + 1)).map (fun i =>
    data.oracle.observe (data.u i))) ++ [data.oracle.observe (data.v n)] ∧
  (∀ i ≤ n, ∀ j ≤ n,
    EuclideanInterpolationGuard data.M data.oracle (data.u i) (data.u j)) ∧
  WasQueried data.trace (data.v n) ∧
  TerminalDescentGuard data.M data.oracle (data.u n) (data.v n)

/-- Source carrier for `lem:ogmg` (E02). -/
noncomputable def FiniteDataOGMGStatement : Prop :=
  ∀ (d n : ℕ) (data : OGMGData d n), OGMGAssumptions data →
    (lpNorm 2 (data.oracle.gradient (data.u n))) ^ (2 : ℕ) ≤
      2 * data.M * (data.oracle.value data.U - data.fstar) /
        (data.theta 0) ^ (2 : ℕ) ∧
    data.theta 0 ≥ ((n : ℝ) + 1) / Real.sqrt 2

/-- The prescribed observation list for the Euclidean gap and OGM-G phases. -/
def euclideanPlannedTrace (inst : PositiveInstance 2 d x0)
    (phaseA : EuclideanGapData d m) (phaseB : OGMGData d n) :
    List (Observation d) :=
  ((List.range m).flatMap (fun k =>
    [inst.oracle.observe (phaseA.y k),
      inst.oracle.observe (phaseA.x (k + 1))])) ++
  ((List.range n).map (fun k =>
    inst.oracle.observe (phaseB.u (k + 1)))) ++
  [inst.oracle.observe (phaseB.v n)]

/-- A guard check formed from the exact oracle observations at its two points. -/
def exactGuardCheck (kind : ObservableGuardKind) (oracle : PairOracle d)
    (x y : Point d) : ObservableGuardCheck d :=
  ⟨kind, oracle.observe x, oracle.observe y⟩

/-- The upper-model, interpolation, and terminal-descent checks of a Euclidean trial. -/
def euclideanGuardSchedule (inst : PositiveInstance 2 d x0)
    (phaseA : EuclideanGapData d m) (phaseB : OGMGData d n) :
    List (ObservableGuardCheck d) :=
  ((List.range m).map (fun k =>
    exactGuardCheck .upperModel inst.oracle (phaseA.y k) (phaseA.x (k + 1)))) ++
  ((List.range (n + 1)).flatMap (fun i =>
    (List.range (n + 1)).map (fun j =>
      exactGuardCheck .interpolation inst.oracle (phaseB.u i) (phaseB.u j)))) ++
  [exactGuardCheck .terminalDescent inst.oracle (phaseB.u n) (phaseB.v n)]

/-- The Euclidean trial stops at the query that makes its first failed guard
checkable.  Phase-A upper-model checks are made after each two-query step;
the ordered interpolation ledger is checked after `u_n` and before the
separate terminal-descent query at `v_n`. -/
def EuclideanScaleTraceStopsAtFailure (inst : PositiveInstance 2 d x0)
    (report : TrialReport d) (phaseA : EuclideanGapData d m)
    (phaseB : OGMGData d n) : Prop :=
  ∀ failed, report.outcome = .scale failed →
    (failed.kind = .upperModel ∧ ∃ k < m,
      report.checkedGuards =
        (euclideanGuardSchedule inst phaseA phaseB).take (k + 1) ∧
      report.trace =
        (euclideanPlannedTrace inst phaseA phaseB).take (2 * (k + 1))) ∨
    (failed.kind = .interpolation ∧
      report.trace =
        (euclideanPlannedTrace inst phaseA phaseB).take (2 * m + n)) ∨
    (failed.kind = .terminalDescent ∧
      report.checkedGuards = euclideanGuardSchedule inst phaseA phaseB ∧
      report.trace = euclideanPlannedTrace inst phaseA phaseB)

/-- The linked Euclidean phases, guard schedule, and chronological trial report contract. -/
def EuclideanTrialOperationalContract (x0 : Point d) (M D : ℝ)
    (inst : PositiveInstance 2 d x0) (report : TrialReport d)
    (phaseA : EuclideanGapData d m) (phaseB : OGMGData d n) : Prop :=
  phaseA.x0 = x0 ∧ phaseA.inst.oracle = inst.oracle ∧
  phaseA.M = M ∧ phaseA.D = D ∧ EuclideanGapDynamics phaseA ∧
  phaseB.oracle = inst.oracle ∧ phaseB.M = M ∧
  phaseB.U = phaseA.x m ∧ OGMGDynamics phaseB ∧
  CheckedGuardsHaveKinds report
    [.upperModel, .interpolation, .terminalDescent] ∧
  report.checkedGuards <+: euclideanGuardSchedule inst phaseA phaseB ∧
  report.trace <+: euclideanPlannedTrace inst phaseA phaseB ∧
  EuclideanScaleTraceStopsAtFailure inst report phaseA phaseB ∧
  (∀ terminal, report.outcome = .success terminal →
    terminal = inst.oracle.observe (phaseB.u n) ∧
    report.trace = euclideanPlannedTrace inst phaseA phaseB ∧
    report.checkedGuards = euclideanGuardSchedule inst phaseA phaseB ∧
    (∀ k < m, GuardRecorded report .upperModel
      (phaseA.y k) (phaseA.x (k + 1))) ∧
    (∀ i ≤ n, ∀ j ≤ n, GuardRecorded report .interpolation
      (phaseB.u i) (phaseB.u j))) ∧
  (∀ terminal, report.outcome = .radius terminal →
    report.trace = euclideanPlannedTrace inst phaseA phaseB ∧
    terminal = inst.oracle.observe (phaseB.u n) ∧
    report.checkedGuards = euclideanGuardSchedule inst phaseA phaseB ∧
    (∀ k < m, GuardRecorded report .upperModel
      (phaseA.y k) (phaseA.x (k + 1))) ∧
    (∀ i ≤ n, ∀ j ≤ n, GuardRecorded report .interpolation
      (phaseB.u i) (phaseB.u j)) ∧
    GuardRecorded report .terminalDescent (phaseB.u n) (phaseB.v n))

/-- Source carrier for `prop:euclideantrial` (E03), retaining the exact
`2m+n+1` accounting and the distinct terminal descent query. -/
noncomputable def EuclideanTrialStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (eps M D : ℝ),
    0 < eps → 0 < M → 0 < D → ∀ (x0 : Point d)
    (cached : CachedPair d),
    ∃ (m n : ℕ) (trial : LocalTrial d),
    m = Nat.ceil (2 * Real.sqrt (M * D / eps)) ∧ n = m ∧
    ∀ inst : PositiveInstance 2 d x0,
    cached.observation = inst.oracle.observe x0 →
    eps < lpNorm 2 (inst.oracle.gradient x0) →
    D ≥ lpNorm 2 (inst.oracle.gradient x0) / M →
    ∃ (report : TrialReport d)
      (phaseA : EuclideanGapData d m) (phaseB : OGMGData d n),
      trial.Executes M D cached inst.oracle report ∧
      TrialCertificate eps 2 M D inst.L inst.R cached inst.oracle report ∧
      EuclideanTrialOperationalContract x0 M D inst report phaseA phaseB ∧
      report.calls ≤ 2 * m + n + 1 ∧
      (report.calls : ℝ) ≤ C * Real.sqrt (M * D / eps)

end V7

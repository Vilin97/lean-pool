/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.EuclideanStatements
import LeanPool.ParameterFreeGradient.V7.AboveTwoStatements

namespace V7

structure AnchorRunData (d : ℕ) where
  acceptedIndex : ℕ
  M : ℕ → ℝ
  D : ℕ → ℝ
  y : ℕ → Point d
  trace : List (Observation d)

noncomputable def normingDirection (q : ℝ) (g : Point d) : Point d :=
  fun i => ((SignType.sign (g i) : ℝ) * |g i| ^ (q - 1)) /
    (lpNorm q g) ^ (q - 1)

noncomputable def NormingDirectionStatement : Prop :=
  ∀ (p : ℝ), 1 < p → ∀ (d : ℕ) (g : Point d),
    0 < lpNorm (conjugateExponent p) g →
    lpNorm p (normingDirection (conjugateExponent p) g) = 1 ∧
    pairing g (normingDirection (conjugateExponent p) g) =
      lpNorm (conjugateExponent p) g

def AnchorTest (oracle : PairOracle d) (x0 : Point d) (G D : ℝ)
    (y : Point d) : Prop :=
  oracle.value y ≤ oracle.value x0 - G * D / 2

/-- The explicit dyadic ray search, including every rejected test and the
first accepted test.  These are algorithm-definition assumptions, not the
named carrier's mathematical conclusions. -/
def AnchorExecution (p : ℝ) (input : MethodInput d) (oracle : PairOracle d)
    (cached : CachedPair d) (run : AnchorRunData d) : Prop :=
  let G := lpNorm (conjugateExponent p) cached.observation.gradient
  (∀ k, run.M k = (2 : ℝ) ^ k * input.M0) ∧
  (∀ k, run.D k = G / run.M k) ∧
  (∀ k, run.y k = input.x0 - run.D k •
    normingDirection (conjugateExponent p) cached.observation.gradient) ∧
  run.trace.length = run.acceptedIndex + 1 ∧
  (∀ k < run.trace.length, ∃ obs,
    (run.trace.drop k).head? = some obs ∧
    obs = oracle.observe (run.y k)) ∧
  (∀ k < run.acceptedIndex,
    ¬ AnchorTest oracle input.x0 G (run.D k) (run.y k)) ∧
  AnchorTest oracle input.x0 G (run.D run.acceptedIndex)
    (run.y run.acceptedIndex)

/-- U03/U13/U14/U19: source carrier for `lem:anchor`, keeping raw `M0`,
accepted `Ma`, and `Da` distinct. -/
noncomputable def AnchorStatement : Prop :=
  ∀ (p : ℝ), 1 < p → ∀ (d : ℕ) (input : MethodInput d)
    (inst : PositiveInstance p d input.x0),
    input.p = p → 0 < input.eps → SecantInitialization input inst.oracle →
    input.M0 ≤ inst.L →
    ∀ cached : CachedPair d,
      cached.observation = inst.oracle.observe input.x0 →
      input.eps < lpNorm (conjugateExponent p) (inst.oracle.gradient input.x0) →
      ∃ run : AnchorRunData d,
        AnchorExecution p input inst.oracle cached run ∧
        let Ma := run.M run.acceptedIndex
        let Da := run.D run.acceptedIndex
        0 < Ma ∧ Da = lpNorm (conjugateExponent p) (inst.oracle.gradient input.x0) / Ma ∧
        Ma < 2 * inst.L ∧ Da ≤ 2 * inst.R ∧
        TraceExact inst.oracle run.trace ∧
        (run.trace.length : ℝ) ≤
          1 + ⌈Real.log (inst.L / input.M0) / Real.log 2⌉

structure ControllerVisit where
  M : ℝ
  D : ℝ

def VisitAt (visits : List ControllerVisit) (i : ℕ)
    (visit : ControllerVisit) : Prop :=
  (visits.drop i).head? = some visit

def ReportAt (reports : List (TrialReport d)) (i : ℕ)
    (report : TrialReport d) : Prop :=
  (reports.drop i).head? = some report

def ControllerPath (G Ma Da : ℝ) (visits : List ControllerVisit)
    (reports : List (TrialReport d)) : Prop :=
  visits.length = reports.length ∧
  visits.head? = some ⟨Ma, Da⟩ ∧
  ∀ i current next report,
    i + 1 < visits.length → VisitAt visits i current →
    VisitAt visits (i + 1) next → ReportAt reports i report →
    match report.outcome with
    | .success _ => False
    | .radius _ => next.M = current.M ∧ next.D = 2 * current.D
    | .scale _ => next.M = 2 * current.M ∧ next.D = G / next.M

def RealizedPathGeometricallyDominated (eps G Ma R : ℝ)
    (visits : List ControllerVisit) : Prop :=
  ∃ (S : ℕ) (lastRadius : ℕ → ℕ),
    let Ms : ℕ → ℝ := fun s => (2 : ℝ) ^ s * Ma
    let Dsj : ℕ → ℕ → ℝ := fun s j => (2 : ℝ) ^ j * G / Ms s
    let kappa : ℕ → ℕ → ℝ := fun s j => Ms s * Dsj s j / eps
    visits = (List.range (S + 1)).flatMap (fun s =>
      (List.range (lastRadius s + 1)).map (fun j =>
        { M := Ms s, D := Dsj s j : ControllerVisit })) ∧
    ∀ a : ℝ, 0 < a →
      (∀ s ≤ S,
        ∑ j ∈ Finset.range (lastRadius s + 1), (kappa s j) ^ a ≤
          (kappa s (lastRadius s)) ^ a / (1 - (2 : ℝ) ^ (-a))) ∧
      (∑ s ∈ Finset.range (S + 1), (Ms s * R / eps) ^ a ≤
        (Ms S * R / eps) ^ a / (1 - (2 : ℝ) ^ (-a)))

def GuardAllowedInRegime (p : ℝ) (kind : ObservableGuardKind) : Prop :=
  if p = 2 then
    kind = .upperModel ∨ kind = .interpolation ∨ kind = .terminalDescent
  else
    kind = .upperModel ∨ kind = .gradient ∨ kind = .cocoercivity

/-- The complete schedule belongs to the specified local routine.  An early
success or first failure consumes a prefix; Radius is legal only after the
entire regime-appropriate schedule has been checked. -/
def GuardLedgerComplete (p : ℝ) (report : TrialReport d)
    (schedule : List (ObservableGuardCheck d)) : Prop :=
  report.checkedGuards <+: schedule ∧
  (∀ check ∈ schedule, GuardAllowedInRegime p check.kind) ∧
  ∀ terminal, report.outcome = .radius terminal →
    report.checkedGuards = schedule

/-- U15--U22: source carrier for `prop:certification`.  Correctness,
visited bounds, reset behavior, and realized-path accounting are distinct
conjuncts. -/
noncomputable def TrialOutcomeCertificationStatement : Prop :=
  ∀ (p : ℝ), 1 < p → ∀ (d : ℕ) (eps G Ma Da L R : ℝ),
    0 < eps → 0 < G → 0 < Ma → 0 < Da →
    Da = G / Ma → Ma < 2 * L → Da ≤ 2 * R →
    ∀ (cached : CachedPair d) (oracle : PairOracle d)
      (visits : List ControllerVisit)
      (reports : List (TrialReport d))
      (schedules : List (List (ObservableGuardCheck d))),
      ControllerPath G Ma Da visits reports →
      schedules.length = reports.length →
      (∀ i < reports.length, ∃ visit report schedule,
        VisitAt visits i visit ∧ ReportAt reports i report ∧
        (schedules.drop i).head? = some schedule ∧
        GuardLedgerComplete p report schedule ∧
        visit.D ≥ G / visit.M ∧
        TrialCertificate eps p visit.M visit.D L R cached oracle report) →
      (∀ visit ∈ visits, visit.M < 2 * L) ∧
      (∀ visit ∈ visits, visit.D ≤ 2 * R) ∧
      RealizedPathGeometricallyDominated eps G Ma R visits

noncomputable def localCostExponent (p : ℝ) : ℝ :=
  if p ≤ 2 then 1 / 2 else p / (p + 2)

/-- G01--G02: source carrier for `lem:amortization`.  Both geometric sums
range over the realized path, never a rectangular product grid. -/
noncomputable def GeometricTrialAmortizationStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (p : ℝ), 1 < p →
  ∃ Cp : ℝ, 0 < Cp ∧ ∀ (eps G L R Ma Da : ℝ),
    0 < eps → eps < G → 0 < L → 0 < R →
    0 < Ma →
    Ma < 2 * L → Da = G / Ma → Da ≤ 2 * R →
    ∀ (S : ℕ) (lastRadius : ℕ → ℕ) (d : ℕ)
      (visits : List ControllerVisit) (reports : List (TrialReport d)),
      let Ms : ℕ → ℝ := fun s => (2 : ℝ) ^ s * Ma
      let Dsj : ℕ → ℕ → ℝ := fun s j => (2 : ℝ) ^ j * G / Ms s
      let kappa : ℕ → ℕ → ℝ := fun s j => Ms s * Dsj s j / eps
      ControllerPath G Ma Da visits reports →
      visits = (List.range (S + 1)).flatMap (fun s =>
        (List.range (lastRadius s + 1)).map (fun j =>
          { M := Ms s, D := Dsj s j : ControllerVisit })) →
      (∀ s ≤ S, Ms s < 2 * L) →
      (∀ s ≤ S, ∀ j ≤ lastRadius s, Dsj s j ≤ 2 * R) →
      (∀ a : ℝ, 0 < a →
        (∀ s ≤ S,
          ∑ j ∈ Finset.range (lastRadius s + 1), (kappa s j) ^ a ≤
            (kappa s (lastRadius s)) ^ a / (1 - (2 : ℝ) ^ (-a))) ∧
        (∑ s ∈ Finset.range (S + 1),
          (Ms s * R / eps) ^ a ≤
            (Ms S * R / eps) ^ a / (1 - (2 : ℝ) ^ (-a)))) ∧
      let a := localCostExponent p
      ((∑ s ∈ Finset.range (S + 1),
        ∑ j ∈ Finset.range (lastRadius s + 1), (kappa s j) ^ a) ≤
        (if p = 2 then C else Cp) * (max 1 (L * R / eps)) ^ a) ∧
      ((∀ i < reports.length, ∃ visit report,
        VisitAt visits i visit ∧ ReportAt reports i report ∧
        (report.calls : ℝ) ≤ (if p = 2 then C else Cp) *
          (visit.M * visit.D / eps) ^ a) →
        (((reports.map (fun report => report.calls)).sum : ℕ) : ℝ) ≤
          (if p = 2 then C else Cp) ^ (2 : ℕ) *
            (max 1 (L * R / eps)) ^ a)

end V7

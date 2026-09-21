/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Euclidean
import LeanPool.ParameterFreeGradient.O3.Stage10EuclideanGuards

/-! Dependency-pure causal machine for the frozen V7 Euclidean trial. -/

namespace V7
namespace Stage1E03

noncomputable local instance e03PropDecidable (q : Prop) : Decidable q :=
  Classical.propDecidable q

noncomputable def CheckHolds (p M : ℝ) (check : ObservableGuardCheck d) : Prop :=
  match check.kind with
  | .upperModel =>
      check.yPair.value ≤ check.xPair.value +
        pairing check.xPair.gradient (check.yPair.point - check.xPair.point) +
        (M / 2) * (lpNorm p (check.yPair.point - check.xPair.point)) ^ (2 : ℕ)
  | .gradient =>
      lpNorm (conjugateExponent p) (check.yPair.gradient - check.xPair.gradient) ≤
        M * lpNorm p (check.yPair.point - check.xPair.point)
  | .cocoercivity =>
      check.xPair.value - check.yPair.value -
          pairing check.yPair.gradient (check.xPair.point - check.yPair.point) ≥
        (lpNorm (conjugateExponent p)
          (check.xPair.gradient - check.yPair.gradient)) ^ (2 : ℕ) / (2 * M)
  | .interpolation =>
      check.xPair.value - check.yPair.value -
        pairing check.yPair.gradient (check.xPair.point - check.yPair.point) -
        (lpNorm 2 (check.xPair.gradient - check.yPair.gradient)) ^ (2 : ℕ) /
          (2 * M) ≥ 0
  | .terminalDescent =>
      check.yPair.value ≤ check.xPair.value -
        (lpNorm 2 check.xPair.gradient) ^ (2 : ℕ) / (2 * M)

noncomputable def upperCheck (oy ox : Observation d) : ObservableGuardCheck d :=
  ⟨.upperModel, oy, ox⟩

noncomputable def interpolationCheck (oi oj : Observation d) :
    ObservableGuardCheck d :=
  ⟨.interpolation, oi, oj⟩

noncomputable def terminalCheck (on ov : Observation d) :
    ObservableGuardCheck d :=
  ⟨.terminalDescent, on, ov⟩

noncomputable def allInterpolationChecks (n : ℕ)
    (obsAt : ℕ → Observation d) : List (ObservableGuardCheck d) :=
  (List.range (n + 1)).flatMap fun i =>
    (List.range (n + 1)).map fun j => interpolationCheck (obsAt i) (obsAt j)

/-- Pure inspection: the error branch is exactly the prefix through the first
failed current-V7 point-carrying guard. -/
noncomputable def evaluateChecks (p M : ℝ) :
    List (ObservableGuardCheck d) →
      Except (List (ObservableGuardCheck d) × ObservableGuardCheck d)
        (List (ObservableGuardCheck d))
  | [] => .ok []
  | check :: checks =>
      if CheckHolds p M check then
        match evaluateChecks p M checks with
        | .ok passed => .ok (check :: passed)
        | .error (prior, failed) => .error (check :: prior, failed)
      else .error ([check], check)

/-- A finite interaction tree indexed by a uniform upper bound on remaining
queries.  `finish` may stop early at any bound. -/
inductive Program (d : ℕ) : ℕ → Type where
  | query {fuel : ℕ} (point : Point d)
      (next : Observation d → Program d fuel) : Program d (fuel + 1)
  | finish {fuel : ℕ} (guards : List (ObservableGuardCheck d))
      (outcome : TrialOutcome d) : Program d fuel

abbrev PackedProgram (d : ℕ) := (fuel : ℕ) × Program d fuel

noncomputable def Program.action : PackedProgram d →
    LocalTrialAction d (PackedProgram d)
  | ⟨_, .finish guards outcome⟩ => .finish guards outcome
  | ⟨fuel + 1, .query point next⟩ =>
      .query point fun obs => ⟨fuel, next obs⟩

noncomputable def Program.eval (oracle : PairOracle d) :
    (fuel : ℕ) → Program d fuel → List (Observation d) → TrialReport d
  | _, .finish guards outcome, history => ⟨history, guards, outcome⟩
  | fuel + 1, .query point next, history =>
      let obs := oracle.observe point
      Program.eval oracle fuel (next obs) (history ++ [obs])

noncomputable def programTrial
    (initial : ℝ → ℝ → CachedPair d → PackedProgram d) : LocalTrial d where
  State := PackedProgram d
  initial := initial
  action := Program.action

theorem Program.runFuel_eq_eval (oracle : PairOracle d)
    (initial : ℝ → ℝ → CachedPair d → PackedProgram d) (fuel : ℕ)
    (program : Program d fuel)
    (history : List (Observation d)) :
    (programTrial initial).runFuel oracle (fuel + 1)
        ⟨fuel, program⟩ history = some (Program.eval oracle fuel program history) := by
  induction fuel generalizing history with
  | zero =>
      cases program with
      | finish guards outcome => rfl
  | succ fuel ih =>
      cases program with
      | finish guards outcome => rfl
      | query point next =>
          rw [show fuel + 1 + 1 = Nat.succ (fuel + 1) by omega]
          change (programTrial initial).runFuel oracle (fuel + 1)
            ⟨fuel, next (oracle.observe point)⟩
              (history ++ [oracle.observe point]) = _
          exact ih (next (oracle.observe point))
            (history ++ [oracle.observe point])

theorem programTrial_executes (oracle : PairOracle d)
    (initial : ℝ → ℝ → CachedPair d → PackedProgram d) (M D : ℝ)
    (cached : CachedPair d) :
    (programTrial initial).Executes M D cached oracle
      (Program.eval oracle (initial M D cached).1 (initial M D cached).2 []) := by
  refine ⟨(initial M D cached).1 + 1, ?_⟩
  exact Program.runFuel_eq_eval oracle initial (initial M D cached).1
      (initial M D cached).2 []

noncomputable def horizon (eps M D : ℝ) : ℕ :=
  Nat.ceil (2 * Real.sqrt (M * D / eps))

theorem horizon_real_ge (eps M D : ℝ) :
    2 * Real.sqrt (M * D / eps) ≤ (horizon eps M D : ℝ) := by
  exact Nat.le_ceil _

theorem one_le_horizon {eps M D : ℝ} (hkappa : 1 ≤ M * D / eps) :
    1 ≤ horizon eps M D := by
  have hsqrt : 1 ≤ Real.sqrt (M * D / eps) := by
    exact (Real.le_sqrt (by positivity) (by positivity)).2
      (by simpa using hkappa)
  have hge := horizon_real_ge eps M D
  exact_mod_cast (show (1 : ℝ) ≤ (horizon eps M D : ℝ) by nlinarith)

theorem horizon_gradient_budget {eps M D : ℝ}
    (heps : 0 < eps) (hM : 0 < M) (hD : 0 < D)
    (hkappa : 1 ≤ M * D / eps) :
    let n := horizon eps M D
    2 * Real.sqrt 2 * M * D /
        (((n : ℝ) + 1) * ((n : ℝ) + 1)) ≤ eps := by
  dsimp only
  let kappa := M * D / eps
  let n := horizon eps M D
  let s : ℝ := (n : ℝ) + 1
  have hk0 : 0 ≤ kappa := le_trans (by norm_num) hkappa
  have hs : 0 < s := by positivity
  have hs2 : 0 < s * s := mul_pos hs hs
  have hceil := horizon_real_ge eps M D
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrtk : 0 ≤ Real.sqrt kappa := Real.sqrt_nonneg _
  have hkSq : (Real.sqrt kappa) ^ 2 = kappa := Real.sq_sqrt hk0
  have hden : 4 * kappa ≤ s * s := by
    change 2 * Real.sqrt kappa ≤ (n : ℝ) at hceil
    dsimp only [s]
    nlinarith
  have hkdef : kappa = M * D / eps := rfl
  have hMD : 4 * M * D ≤ eps * (s * s) := by
    rw [hkdef] at hden
    have h := mul_le_mul_of_nonneg_left hden heps.le
    field_simp [ne_of_gt heps] at h
    nlinarith
  have hnum : 2 * Real.sqrt 2 * M * D ≤ eps * (s * s) := by
    have hMD0 : 0 ≤ M * D := mul_nonneg hM.le hD.le
    nlinarith
  exact (div_le_iff₀ hs2).2 (by
    simpa only [kappa, n, s] using hnum)

noncomputable def nextEstimateState (M : ℝ) (x0 : Point d) (k : ℕ)
    (state : O3.EuclideanEstimateState d) (oy : Observation d) :
    O3.EuclideanEstimateState d :=
  let A := O3.euclideanA k
  let a := O3.euclideanWeight A
  let sNext := state.cumulativeGradient + a • oy.gradient
  let zNext := O3.Stage8EuclideanMinimizer.euclideanPsiMinimizer M x0 sNext
  ⟨O3.euclideanBarycenter A a state.accelerated zNext, sNext⟩

noncomputable def estimateQuery (M : ℝ) (x0 : Point d) (k : ℕ)
    (state : O3.EuclideanEstimateState d) : Point d :=
  O3.euclideanBarycenter (O3.euclideanA k)
    (O3.euclideanWeight (O3.euclideanA k)) state.accelerated
    (O3.Stage8EuclideanMinimizer.euclideanPsiMinimizer M x0
      state.cumulativeGradient)

noncomputable def ogmgStep (n : ℕ) (M : ℝ) (i : ℕ)
    (state : O3.OGMGExecutionState d) (oi : Observation d) :
    O3.OGMGExecutionState d :=
  let v := state.current - M⁻¹ • oi.gradient
  let momentum :=
    ((O3.stage9Theta n i - 1) * (2 * O3.stage9Theta n (i + 1) - 1)) /
      (O3.stage9Theta n i * (2 * O3.stage9Theta n i - 1))
  let correction :=
    (2 * O3.stage9Theta n (i + 1) - 1) /
      (2 * O3.stage9Theta n i - 1)
  ⟨v + momentum • (v - state.previousV) + correction • (v - state.current), v⟩

noncomputable def terminalProgram (eps M : ℝ) (n : ℕ)
    (obsAt : ℕ → Observation d) (exec : O3.OGMGExecutionState d)
    (guards : List (ObservableGuardCheck d)) : Program d 1 :=
  let on := obsAt n
  let v := exec.current - M⁻¹ • on.gradient
  .query v fun ov =>
    let terminal := terminalCheck on ov
    let allGuards := guards ++ [terminal]
    if CheckHolds 2 M terminal then
      if lpNorm 2 on.gradient ≤ eps then
        .finish allGuards (.success on)
      else .finish allGuards (.radius on)
    else .finish allGuards (.scale terminal)

noncomputable def phaseBProgram (eps M : ℝ) (n i : ℕ)
    (exec : O3.OGMGExecutionState d) (obsAt : ℕ → Observation d)
    (guards : List (ObservableGuardCheck d)) :
    (fuel : ℕ) → Program d (fuel + 1)
  | 0 =>
      let checks := allInterpolationChecks n obsAt
      match evaluateChecks 2 M checks with
      | .error (prior, failed) => .finish (guards ++ prior) (.scale failed)
      | .ok passed => terminalProgram eps M n obsAt exec (guards ++ passed)
  | fuel + 1 =>
      let next := ogmgStep n M i exec (obsAt i)
      .query next.current fun oi =>
        phaseBProgram eps M n (i + 1) next
          (fun j => if j = i + 1 then oi else obsAt j) guards fuel

def phaseABudget (n : ℕ) : ℕ → ℕ
  | 0 => n + 1
  | fuel + 1 => phaseABudget n fuel + 2

noncomputable def phaseAProgram (eps M : ℝ) (x0 : Point d) (n k : ℕ)
    (estimate : O3.EuclideanEstimateState d)
    (last : Option (Observation d))
    (guards : List (ObservableGuardCheck d)) :
    (fuel : ℕ) → Program d (phaseABudget n fuel)
  | 0 =>
      match last with
      | none => .finish guards (.scale
          (upperCheck ⟨x0, 0, 0⟩ ⟨x0, 0, 0⟩))
      | some oU =>
          let exec : O3.OGMGExecutionState d :=
            ⟨estimate.accelerated, estimate.accelerated⟩
          phaseBProgram eps M n 0 exec (fun _ => oU) guards n
  | fuel + 1 =>
      .query (estimateQuery M x0 k estimate) fun oy =>
        let next := nextEstimateState M x0 k estimate oy
        .query next.accelerated fun ox =>
          let check := upperCheck oy ox
          if CheckHolds 2 M check then
            phaseAProgram eps M x0 n (k + 1) next (some ox)
              (guards ++ [check]) fuel
          else .finish (guards ++ [check]) (.scale check)

noncomputable def euclideanLocalTrial (eps : ℝ) (x0 : Point d) (n : ℕ) :
    LocalTrial d :=
  programTrial fun M _D _cached =>
    ⟨phaseABudget n n,
      phaseAProgram eps M x0 n 0 ⟨x0, 0⟩ none [] n⟩

end Stage1E03
end V7

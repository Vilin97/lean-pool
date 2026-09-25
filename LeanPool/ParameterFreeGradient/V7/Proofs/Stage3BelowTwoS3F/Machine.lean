/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage3BelowTwoS3F.DualTrajectory

/-!
Finite causal query programs implementing the below-two primal and dual phases.
-/

@[expose] public section

namespace V7.Stage3BelowTwoS3F

/-- Classical proposition decisions used locally by the below-two trial machine. -/
noncomputable local instance machinePropDecidable (q : Prop) : Decidable q :=
  Classical.propDecidable q

/-- The observed physical gradient rescaled into normalized trial coordinates. -/
noncomputable def normalizedGradient (M D : ℝ) (obs : Observation d) : Point d :=
  (1 / (M * D)) • obs.gradient

/-- The cocoercivity guard formed from consecutive observations. -/
noncomputable def cocoCheck (before after : Observation d) :
    ObservableGuardCheck d := ⟨.cocoercivity, before, after⟩

/-- The cocoercivity inequality reconstructed from a guard's two recorded observations. -/
noncomputable def checkHolds (p M : ℝ) (check : ObservableGuardCheck d) : Prop :=
  BregmanRemainder
      { value := fun x => if x = check.xPair.point then check.xPair.value
          else if x = check.yPair.point then check.yPair.value else 0
        gradient := fun x => if x = check.xPair.point then check.xPair.gradient
          else if x = check.yPair.point then check.yPair.gradient else 0 }
      check.xPair.point check.yPair.point ≥
    (lpNorm (conjugateExponent p)
      (check.xPair.gradient - check.yPair.gradient)) ^ (2 : ℕ) / (2 * M)

/-- The form actually evaluated by the machine, written directly from the two
returned exact pairs. -/
noncomputable def cocoPairHolds (p M : ℝ) (before after : Observation d) : Prop :=
  before.value - after.value -
      pairing after.gradient (before.point - after.point) ≥
    (lpNorm (conjugateExponent p) (before.gradient - after.gradient)) ^ (2 : ℕ) /
      (2 * M)

/-- A finite oracle-query program indexed by an upper bound on its remaining queries. -/
inductive Program (d : ℕ) : ℕ → Type where
  | query {fuel : ℕ} (point : Point d)
      (next : Observation d → Program d fuel) : Program d (fuel + 1)
  | finish {fuel : ℕ} (guards : List (ObservableGuardCheck d))
      (outcome : TrialOutcome d) : Program d fuel

/-- A finite query program paired with its query bound. -/
abbrev PackedProgram (d : ℕ) := (fuel : ℕ) × Program d fuel

/-- The next local-trial action exposed by a packed finite program. -/
noncomputable def Program.action : PackedProgram d →
    LocalTrialAction d (PackedProgram d)
  | ⟨_, .finish guards outcome⟩ => .finish guards outcome
  | ⟨fuel + 1, .query point next⟩ => .query point fun obs => ⟨fuel, next obs⟩

/-- The report obtained by evaluating the finite program against an oracle. -/
noncomputable def Program.eval (oracle : PairOracle d) :
    (fuel : ℕ) → Program d fuel → List (Observation d) → TrialReport d
  | _, .finish guards outcome, history => ⟨history, guards, outcome⟩
  | fuel + 1, .query point next, history =>
      let obs := oracle.observe point
      Program.eval oracle fuel (next obs) (history ++ [obs])

/-- The local trial induced by a family of initial finite query programs. -/
noncomputable def programTrial
    (initial : ℝ → ℝ → CachedPair d → PackedProgram d) : LocalTrial d where
  State := PackedProgram d
  initial := initial
  action := Program.action

theorem Program.runFuel_eq_eval (oracle : PairOracle d)
    (initial : ℝ → ℝ → CachedPair d → PackedProgram d) (fuel : ℕ)
    (program : Program d fuel) (history : List (Observation d)) :
    (programTrial initial).runFuel oracle (fuel + 1) ⟨fuel, program⟩ history =
      some (Program.eval oracle fuel program history) := by
  induction fuel generalizing history with
  | zero => cases program; rfl
  | succ fuel ih =>
      cases program with
      | finish guards outcome => rfl
      | query point next =>
          rw [show fuel + 1 + 1 = Nat.succ (fuel + 1) by omega]
          change (programTrial initial).runFuel oracle (fuel + 1)
            ⟨fuel, next (oracle.observe point)⟩
              (history ++ [oracle.observe point]) = _
          exact ih (next (oracle.observe point)) (history ++ [oracle.observe point])

theorem programTrial_executes (oracle : PairOracle d)
    (initial : ℝ → ℝ → CachedPair d → PackedProgram d) (M D : ℝ)
    (cached : CachedPair d) :
    (programTrial initial).Executes M D cached oracle
      (Program.eval oracle (initial M D cached).1 (initial M D cached).2 []) := by
  refine ⟨(initial M D cached).1 + 1, ?_⟩
  exact Program.runFuel_eq_eval oracle initial (initial M D cached).1
    (initial M D cached).2 []

/-- The below-two dual query program with early accuracy or guard-failure termination. -/
noncomputable def dualProgram (p eps M D : ℝ) (n k : ℕ)
    (center : Point d) (q r : Point d) (G : VectorSeq d)
    (previous : Observation d) (guards : List (ObservableGuardCheck d)) :
    (fuel : ℕ) → Program d fuel
  | 0 => .finish guards (.radius previous)
  | fuel + 1 =>
      let qNext := q - increment n (n - 1 - k) • belowMirrorMap p r
      .query (center + D • qNext) fun obs =>
        if lpNorm (conjugateExponent p) obs.gradient ≤ eps then
          .finish guards (.success obs)
        else
          let check := cocoCheck previous obs
          let guardsNext := guards ++ [check]
          if cocoPairHolds p M previous obs then
            let GNext : VectorSeq d := fun i =>
              if i = k + 1 then normalizedGradient M D obs else G i
            let rNext := r - weightedSum (k + 2)
              (fun i => coeffB n (n - i) (n - 1 - k)) GNext
            dualProgram p eps M D n (k + 1) center qNext rNext GNext obs
              guardsNext fuel
          else .finish guardsNext (.scale check)

/-- The remaining primal query budget plus the complete dual query budget. -/
def phaseOneBudget (n : ℕ) : ℕ → ℕ
  | 0 => n
  | fuel + 1 => phaseOneBudget n fuel + 1

/-- The below-two primal query program that passes its endpoint to the dual phase. -/
noncomputable def phaseOneProgram (p eps M D : ℝ) (x0 : Point d) (n k : ℕ)
    (state : PrimalState d) (previous : Observation d)
    (guards : List (ObservableGuardCheck d)) :
    (fuel : ℕ) → Program d (phaseOneBudget n fuel)
  | 0 =>
      let center := previous.point
      let G0 := normalizedGradient M D previous
      let G : VectorSeq d := fun i => if i = 0 then G0 else 0
      let r0 := -(coeffB n n n) • G0
      dualProgram p eps M D n 0 center 0 r0 G previous guards n
  | fuel + 1 =>
      let sNext := state.s - increment n k • normalizedGradient M D previous
      let vNext := belowMirrorMap p sNext
      let xNext :=
        (weight n k / weight n (k + 1)) • state.x +
        (increment n (k + 1) / weight n (k + 1)) • vNext +
        (increment n k / weight n (k + 1)) • (vNext - state.v)
      .query (x0 + D • xNext) fun obs =>
        if lpNorm (conjugateExponent p) obs.gradient ≤ eps then
          .finish guards (.success obs)
        else
          let check := cocoCheck previous obs
          let guardsNext := guards ++ [check]
          if cocoPairHolds p M previous obs then
            phaseOneProgram p eps M D x0 n (k + 1) ⟨sNext, vNext, xNext⟩
              obs guardsNext fuel
          else .finish guardsNext (.scale check)

/-- The complete below-two local trial initialized with the cached starting observation. -/
noncomputable def belowLocalTrial (p eps : ℝ) (x0 : Point d) (n : ℕ) :
    LocalTrial d :=
  programTrial fun M D cached =>
    ⟨phaseOneBudget n n, phaseOneProgram p eps M D x0 n 0 ⟨0, 0, 0⟩
      cached.observation [] n⟩

end V7.Stage3BelowTwoS3F

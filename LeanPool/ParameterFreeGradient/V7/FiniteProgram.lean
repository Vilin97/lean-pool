/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.TrialInterfaces

/-! # Finite query programs shared by the geometry-specific trial machines -/

@[expose] public section

namespace V7.CausalProgram

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

end V7.CausalProgram

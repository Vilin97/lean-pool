/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage4AboveTwoFinalTrial.Trajectory

/-!
Finite causal query programs implementing the above-two primal and dual phases.
-/

namespace V7.Stage4AboveTwoFinalTrial

open V7.Stage3BelowTwoS3F

/-- Classical proposition decisions used locally by the above-two trial machine. -/
noncomputable local instance machinePropDecidable (q : Prop) : Decidable q :=
  Classical.propDecidable q

/-- The above-two dual query program with early accuracy or guard-failure termination. -/
noncomputable def dualProgram (p eps M D eta : ℝ) (n k : ℕ)
    (center : Point d) (q r : Point d) (G : VectorSeq d)
    (previous : Observation d) (guards : List (ObservableGuardCheck d)) :
    (fuel : ℕ) → Program d fuel
  | 0 => .finish guards (.radius previous)
  | fuel + 1 =>
      let qNext := q - increment p eta n (n - 1 - k) • aboveMirrorMap p r
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
              (fun i => coeffB p eta n (n - i) (n - 1 - k)) GNext
            dualProgram p eps M D eta n (k + 1) center qNext rNext GNext obs
              guardsNext fuel
          else .finish guardsNext (.scale check)

/-- The remaining primal query budget plus the prescribed dual horizon. -/
def phaseOneBudget (nD : ℕ) : ℕ → ℕ
  | 0 => nD
  | fuel + 1 => phaseOneBudget nD fuel + 1

/-- The above-two primal query program that initializes the dual phase at its endpoint. -/
noncomputable def phaseOneProgram (p eps M D eta₁ eta₂ : ℝ)
    (x0 : Point d) (n₁ n₂ k : ℕ) (state : PrimalState d)
    (previous : Observation d) (guards : List (ObservableGuardCheck d)) :
    (fuel : ℕ) → Program d (phaseOneBudget n₂ fuel)
  | 0 =>
      let center := previous.point
      let G0 := normalizedGradient M D previous
      let G : VectorSeq d := fun i => if i = 0 then G0 else 0
      let r0 := -(coeffB p eta₂ n₂ n₂ n₂) • G0
      dualProgram p eps M D eta₂ n₂ 0 center 0 r0 G previous guards n₂
  | fuel + 1 =>
      let sNext := state.s - increment p eta₁ n₁ k • normalizedGradient M D previous
      let vNext := aboveMirrorMap p sNext
      let xNext :=
        (weight p eta₁ n₁ k / weight p eta₁ n₁ (k + 1)) • state.x +
        (increment p eta₁ n₁ (k + 1) / weight p eta₁ n₁ (k + 1)) • vNext +
        (increment p eta₁ n₁ k / weight p eta₁ n₁ (k + 1)) •
          (vNext - state.v)
      .query (x0 + D • xNext) fun obs =>
        if lpNorm (conjugateExponent p) obs.gradient ≤ eps then
          .finish guards (.success obs)
        else
          let check := cocoCheck previous obs
          let guardsNext := guards ++ [check]
          if cocoPairHolds p M previous obs then
            phaseOneProgram p eps M D eta₁ eta₂ x0 n₁ n₂ (k + 1)
              ⟨sNext, vNext, xNext⟩ obs guardsNext fuel
          else .finish guardsNext (.scale check)

/-- The complete above-two local trial with its primal and dual horizons. -/
noncomputable def aboveLocalTrial (p eps : ℝ) (x0 : Point d)
    (nf nd : ℕ) : LocalTrial d :=
  programTrial fun M D cached =>
    ⟨phaseOneBudget nd nf,
      phaseOneProgram p eps M D (etaF p) (etaD p eps M D) x0 nf nd 0
        ⟨0, 0, 0⟩ cached.observation [] nf⟩

end V7.Stage4AboveTwoFinalTrial

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.BKARForestFormula.BKAR
import LeanPool.BKARForestFormula.Audit.ForestFormula.SolutionBasic

/-!
# BKAR forest formula — Solution

This file proves the byte-identical challenge statement of
`Audit/ForestFormula/Challenge.lean` from the repository flagship
`BKAR.bkar_formula_forestIndex_cube_contributions`, through the bridge lemmas of
`Audit/ForestFormula/SolutionBasic.lean`.

The theorem statement below is character-for-character identical to the one in
`Challenge.lean` (same namespace `BKARMirror`, same mirror vocabulary); only the
proof differs (`sorry` there, a real proof here).

`#print axioms` gives exactly `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section
open MeasureTheory

namespace BKARMirror

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Challenge statement** (Mathlib-only): the BKAR forest interpolation formula. -/
theorem bkar_formula_forestIndex_cube_contributions (ρ : (Edge V → ℝ) → ℝ)
    (hρ : ContDiffHyp ρ) :
    ρ (fun _ => 1) = ∑ J : ForestIndex V, cubeContribution J ρ :=
  calc ρ (fun _ => 1)
      = ρ BKAR.oneConfig := by rw [oneConfig_bridge]
    _ = ∑ I : BKAR.ForestIndex V, I.cubeContribution ρ :=
        BKAR.bkar_formula_forestIndex_cube_contributions ρ hρ
    _ = ∑ J : ForestIndex V, cubeContribution J ρ := (sum_bridge ρ hρ).symm

end BKARMirror

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/

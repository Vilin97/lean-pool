/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.BKARForestFormula.BKAR
public import LeanPool.BKARForestFormula.Audit.ForestFormula.SolutionBasic

/-!
# BKAR forest formula — Solution

This file proves the mirror statement below from the repository flagship
`BKAR.bkar_formula_forestIndex_cube_contributions`, through the bridge lemmas of
`Audit/ForestFormula/SolutionBasic.lean`.

The mirror originates in `Audit/ForestFormula/Challenge.lean` in
`scottnarmstrong/bkarforestformula`, commit
`a07f44a534240fe6339558951dd78a19e4ef7c51`. That upstream statement can be inspected
at the pinned revision; its placeholder proof is omitted from Lean Pool. The
local statement vocabulary lives in `SolutionBasic.lean`, and the bridge lemmas
and proof below establish the formula for that vocabulary. This port does not
maintain an automated comparison with the upstream challenge.

`#print axioms` gives exactly `[propext, Classical.choice, Quot.sound]`.
-/

@[expose] public section

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

/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import Mathlib.Tactic.NormNum
import LeanPool.OrdvecFormalization.BitmapCalibration
import LeanPool.OrdvecFormalization.OverlapNull

/-!
# Concrete theorem-shape examples

This file keeps a tiny concrete instantiation of the final bitmap theorem
in the build so API drift is easy to spot.
-/

open scoped NNReal

namespace OrdvecFormalization

/-- A small feasible FNCH parameter set. -/
def exampleFNCHParams : FNCHParams where
  N := 10
  k := 4
  draws := 3
  k_le_N := by norm_num
  draws_le_N := by norm_num

/-- A balanced prior for example statements. -/
noncomputable def balancedPrior : Prior where
  prob := (1 / 2 : ℝ≥0)
  le_one := by norm_num

theorem balancedPrior_pos : 0 < balancedPrior.prob := by
  norm_num [balancedPrior]

/-- Unit false-decision costs for example statements. -/
def unitDecisionCosts : DecisionCosts where
  falseAccept := 1
  falseReject := 1

theorem unitDecisionCosts_falseReject_mul_balancedPrior_pos :
    0 < unitDecisionCosts.falseReject * balancedPrior.prob := by
  norm_num [balancedPrior, unitDecisionCosts]

/-- A tiny `1`-active bitmap query in three coordinates. -/
def exampleBitmapQuery : Finset (BitmapCoord 3) :=
  {0}

@[simp]
theorem card_exampleBitmapQuery : exampleBitmapQuery.card = 1 := by
  simp [exampleBitmapQuery]

end OrdvecFormalization

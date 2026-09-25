/-
Copyright (c) 2026 Yoshito Ishiki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshito Ishiki
-/
module

public import LeanPool.ScottishBook155.StageSystem


/-!
# The initial protected stage

This file upgrades the elementary bent-map calculation to an actual map
between real Banach spaces carrying the invariant used by the transfinite
construction.
-/

@[expose] public section

namespace ScottishBook155

open WithLp

/-- The bent seed as a map into the genuine l-one Banach sum. -/
noncomputable def bentMapL1 (t : ℝ) : OneSum ℝ :=
  toLp 1 (bentMap t)

theorem bentMapL1_injective : Function.Injective bentMapL1 := by
  intro s t h
  apply bentMap_injective
  exact WithLp.toLp_injective 1 h

theorem bentMapL1_dist_eq (s t : ℝ) :
    dist (bentMapL1 s) (bentMapL1 t) = l1Dist (bentMap s) (bentMap t) := by
  rw [oneSum_dist_eq]
  rfl

theorem bentMapL1_preservesUpTo :
    PreservesUpTo ((1 : ℝ) / 2) bentMapL1 := by
  intro s t hst
  rw [bentMapL1_dist_eq, Real.dist_eq]
  exact bentMap_short s t (by simpa [Real.dist_eq] using hst)

theorem bentMapL1_contraction :
    dist (bentMapL1 (-1)) (bentMapL1 2) = 1 ∧
      dist (-1 : ℝ) 2 = 3 := by
  rw [bentMapL1_dist_eq, Real.dist_eq]
  simpa using bentMap_contraction

/-- Stage zero of the claim-14 recursion. -/
noncomputable def bentSeedStage : ProtectedStage ((1 : ℝ) / 2) where
  source := RealBanachSpace.ofType ℝ
  target := RealBanachSpace.ofType (OneSum ℝ)
  map := bentMapL1
  injective := bentMapL1_injective
  preservesUpTo := bentMapL1_preservesUpTo

end ScottishBook155

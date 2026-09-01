/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.L1PowerSeries
import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.L1Division
import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.NormalizedCoefficients

/-!
# Evaluation of finite-support `ℓ¹` coefficient sequences

These lemmas translate the normalized sequence factorization into the monic
polynomial identity used by the public preparation witness.
-/

open Finset
open scoped ENNReal NNReal Topology
noncomputable section


namespace ClassicalComplexWPT

theorem evalL1PowerSeries_smul (c : ℂ) (a : L1Sequence) (w : ℂ) :
    evalL1PowerSeries (c • a) w = c * evalL1PowerSeries a w := by
  change l1EvalOperator w (c • a) = _
  rw [map_smul]
  rfl

theorem evalL1PowerSeries_monomialSeq (d : ℕ) {w : ℂ} (hw : ‖w‖ < 1) :
    evalL1PowerSeries (monomialSeq d) w = w ^ d := by
  rw [evalL1PowerSeries_eq_tsum _ hw, tsum_eq_single d]
  · simp [monomialSeq_apply_same]
  · intro k hkd
    simp [monomialSeq_apply_ne hkd]

theorem evalL1PowerSeries_eq_sum_fin_of_highShift_eq_zero
    (d : ℕ) (a : L1Sequence) (ha : seqHighShift d a = 0)
    {w : ℂ} (hw : ‖w‖ < 1) :
    evalL1PowerSeries a w = ∑ i : Fin d, a i * w ^ (i : ℕ) := by
  rw [evalL1PowerSeries_eq_tsum _ hw]
  let F : ℕ → ℂ := fun k ↦ a k * w ^ k
  change (∑' k : ℕ, F k) = ∑ i : Fin d, F i
  rw [Fin.sum_univ_eq_sum_range F d]
  apply tsum_eq_sum
  intro k hk
  simp only [Finset.mem_range, not_lt] at hk
  have hcoord := congrArg (fun b : L1Sequence ↦ b (k - d)) ha
  change a ((k - d) + d) = 0 at hcoord
  rw [Nat.sub_add_cancel hk] at hcoord
  dsimp only [F]
  rw [hcoord, zero_mul]

end ClassicalComplexWPT

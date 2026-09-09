/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SolutionDefinitions
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

@[expose] public section

/-! Compact smooth data satisfy the independent challenge's rapid-decay condition. -/

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace Euler

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

theorem initialVelocityConditionDecay_of_compact
    (u₀ : ℝ³ → ℝ³) (hs : ContDiff ℝ ∞ u₀) (hc : HasCompactSupport u₀)
    (hd : ∀ x, divergence u₀ x = 0) : InitialVelocityConditionDecay u₀ := by
  refine ⟨⟨hd, hs⟩, ?_⟩
  intro m K
  let g : ℝ³ → ℝ := fun x => (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ m u₀ x‖
  have hpos (x : ℝ³) : 0 < 1 + ‖x‖ := by positivity
  have hg : Continuous g :=
    ((continuous_const.add continuous_norm).rpow_const
      (fun x => Or.inl (hpos x).ne')).mul
      ((hs.continuous_iteratedFDeriv (by simp)).norm)
  have hgc : HasCompactSupport g := (hc.iteratedFDeriv m).norm.mul_left
  obtain ⟨x₀, hx₀⟩ := hg.exists_forall_ge_of_hasCompactSupport hgc
  refine ⟨g x₀, fun x => (le_div_iff₀ (Real.rpow_pos_of_pos (hpos x) K)).mpr ?_⟩
  simpa only [g, mul_comm] using hx₀ x

end Euler

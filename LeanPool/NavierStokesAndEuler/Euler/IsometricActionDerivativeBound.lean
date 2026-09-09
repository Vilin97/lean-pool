/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Operator.Basic
import LeanPool.NavierStokesAndEuler.Euler.IsometricActionCalculus
import Mathlib.Analysis.Calculus.MeanValue

/-! A true orbit derivative gives a global increment bound for a linear isometric action. -/

@[expose] public section


noncomputable section

namespace EulerIsometricAction

variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_sub_le_of_hasFDerivAt (τ : P → E →ₗᵢ[ℝ] E)
    (hadd : ∀ a b u, τ a (τ b u) = τ (a + b) u) (hzero : ∀ u, τ 0 u = u)
    (u : E) (D : P →L[ℝ] E) (h : HasFDerivAt (fun a => τ a u) D 0) (a : P) :
    ‖τ a u-u‖ ≤ ‖D‖*‖a‖ := by
  have hb (b : P) : ‖(τ b).toContinuousLinearMap.comp D‖ ≤ ‖D‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometry.norm_map] using D.le_opNorm v
  have hh := (convex_univ : Convex ℝ (Set.univ : Set
      P)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun b _ => (hasFDerivAt_all τ hadd u D h b).hasFDerivWithinAt)
    (fun b _ => hb b) (Set.mem_univ (0 : P)) (Set.mem_univ a)
  simpa only [hzero, sub_zero] using hh

end EulerIsometricAction

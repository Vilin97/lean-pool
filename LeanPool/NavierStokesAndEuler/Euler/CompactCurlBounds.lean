/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanCutoffCurlBound
public import LeanPool.NavierStokesAndEuler.Euler.SolutionDefinitions
import LeanPool.NavierStokesAndEuler.Euler.ClassicalBridge
import LeanPool.NavierStokesAndEuler.Euler.CompactSmoothBounds
import LeanPool.NavierStokesAndEuler.Euler.CurlTimeDerivative

/-! Joint smoothness bounds the actual spatial vorticity on every fixed
compact spatial set and every closed finite time interval. -/

@[expose] public section


noncomputable section


open Set EulerSmoothLimit EulerMeanBoundary EulerMeanCutoffCurl

namespace Euler.EulerExistenceAndSmoothnessR3

variable {u₀ : Space → Space} {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}
  (h : EulerExistenceAndSmoothnessR3 u₀ v p)

include h

theorem vorticity_bounded_on_compact (K : Set Space) (hK : IsCompact K) (T : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      ‖vectorCurl (v · t) x‖ ≤ M := by
  obtain ⟨C, hC⟩ := h.spatial_fderiv_bounded_on_compact K hK T
  refine ⟨‖ComparatorBridge.curlMatrixCLM‖ * max C 0,
    mul_nonneg (norm_nonneg ComparatorBridge.curlMatrixCLM) (le_max_right _ _), ?_⟩
  intro t ht x hx
  rw [vectorCurl_eq_matrix _ x ((h.velocity_contDiff t ht.1).differentiable (by simp) x)]
  change ‖ComparatorBridge.curlMatrixCLM (fderiv ℝ (v · t) x)‖ ≤ _
  exact (ComparatorBridge.curlMatrixCLM.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left ((hC x hx t ht).trans (le_max_left _ _))
      (norm_nonneg ComparatorBridge.curlMatrixCLM))

end Euler.EulerExistenceAndSmoothnessR3

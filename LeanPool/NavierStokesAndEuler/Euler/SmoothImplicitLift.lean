/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

@[expose] public section

/-! A continuous, already constructed solution of a smooth identity is
smooth when the derivative in its value variable is invertible. The local
inverse theorem proves regularity; no new solution is postulated. -/

noncomputable section

open Filter Function
open scoped Topology ContDiff

namespace EulerSmoothImplicitLift

variable {P E F : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffAt_of_identity
    (Y : P → E) (G : E → F) (H : P → F) (x : P) (n : ℕ∞ω)
    (hn : n ≠ 0) (hY : ContinuousAt Y x)
    (hG : ContDiffAt ℝ n G (Y x)) (hH : ContDiffAt ℝ n H x)
    (L : E ≃L[ℝ] F) (hL : HasFDerivAt G (L : E →L[ℝ] F) (Y x))
    (heq : ∀ y, G (Y y) = H y) : ContDiffAt ℝ n Y x := by
  let J := hG.localInverse hL hn
  have hJ : ContDiffAt ℝ n J (H x) := by
    rw [← heq x]
    exact hG.to_localInverse hL hn
  have hleft : ∀ᶠ z in 𝓝 (Y x), J (G z) = z :=
    (hG.hasStrictFDerivAt' hL hn).eventually_left_inverse
  have he : Y =ᶠ[𝓝 x] J ∘ H := by
    filter_upwards [hY.tendsto.eventually hleft] with y hy
    change Y y = J (H y)
    rw [← heq y]
    exact hy.symm
  exact (hJ.comp x hH).congr_of_eventuallyEq he

end EulerSmoothImplicitLift

/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.ConditionalTwoPointCalibration
import LeanPool.Feige.KernelAveraging

/-!
# Calibration after latent mixing

This is the measure-theoretic averaging step in the proof of Theorem 2.1.
It is kept separate from the construction of the latent law: any probability
measure on augmented parameters that is almost surely admissible can be used.
-/

open MeasureTheory ProbabilityTheory

namespace Feige

noncomputable section

/-- Mixing conditionally calibrated augmented two-point products preserves
the rejection bound. -/
theorem augmentedMixture_rejection_le
    (htwo : TwoPointRejectionBound)
    {n : ℕ}
    (ν : Measure (Fin n → AugmentedTwoPointParams))
    [IsProbabilityMeasure ν]
    (hν : ∀ᵐ p ∂ν, AugmentedParamsNonnegative p)
    {α : ℝ} (hα : 0 ≤ α) :
    (recursiveAugmentedKernel n ∘ₘ ν).real
        {y | dirichletK y ≤ α} ≤ α := by
  apply measureReal_bind_apply_le
    (recursiveAugmentedKernel n) ν
    (measurableSet_dirichletK_le α) hα
  filter_upwards [hν] with p hp
  exact recursiveAugmentedKernel_rejection_le htwo p hp hα

end

end Feige

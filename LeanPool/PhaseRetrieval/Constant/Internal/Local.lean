/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
/-
  # Local.lean
  Transparent statement of the local phase-aligned Fock-space phase retrieval estimate.

  This is the local analogue of `Basic.lean`, but without the ad hoc reality
  condition at the origin. Instead, when `p` is small in normalized Gaussian `L²`,
  we are allowed to rotate `1 + p` by a unit complex number.

  **Theorem (local phase-aligned coercivity).**
  One may take the explicit constants `δ = 1 / 4601` and `M = 23003`. If

    `(1 / π) ∫_ℂ |p(z)|² exp(−‖z‖²) dm(z) ≤ (1 / 4601)²`,

  then there exists `w ∈ ℂ` with `|w| = 1` such that

    `∫_ℂ |w (1 + p(z)) − 1|² exp(−‖z‖²) dm(z)
      ≤ 23003² ∫_ℂ ||1 + p(z)| − 1|² exp(−‖z‖²) dm(z)`.
-/
import LeanPool.PhaseRetrieval.Constant.Internal.LocalHelpers

/-! # Local -/


open FockSPR MeasureTheory Complex Real Polynomial

noncomputable section

namespace FockSPR

/-
## Local Main Theorem (transparent statement)

There exist explicit constants `δ = 1 / 4601` and `M = 23003` such that whenever

  `(1 / π) ∫ |p(z)|² exp(−‖z‖²) dm ≤ δ²`,

there exists a unit complex number `w` with

  `∫ |w (1 + p(z)) − 1|² exp(−‖z‖²) dm ≤ M² ∫ ||1 + p(z)| − 1|² exp(−‖z‖²) dm`.
-/
theorem LocalFockSPR_constants :
    ∃ δ M : ℝ,
      δ = (1 / 4601 : ℝ) ∧
      M = (23003 : ℝ) ∧
      ∀ p : Polynomial ℂ,
        (1 / Real.pi) * ∫ z : ℂ, ‖p.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ≤ δ ^ 2 →
          ∃ w : ℂ, ‖w‖ = 1 ∧
            ∫ z : ℂ, ‖w * (1 + p.eval z) - 1‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ≤
              M ^ 2 * ∫ z : ℂ, (|‖1 + p.eval z‖ - 1|) ^ 2 * Real.exp (-‖z‖ ^ 2) := by
  exact ⟨(1 / 4601 : ℝ), (23003 : ℝ), rfl, rfl,
    fun p hsmall => LocalFockSPR_of_small_norm_exists_phase p hsmall⟩

theorem LocalFockSPR_exists_phase
    (p : Polynomial ℂ)
    (hsmall :
      (1 / Real.pi) * ∫ z : ℂ, ‖p.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ≤
        (1 / 4601 : ℝ) ^ 2) :
    ∃ w : ℂ, ‖w‖ = 1 ∧
      ∫ z : ℂ, ‖w * ((1 : ℂ) + p.eval z) - 1‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ≤
        23003 ^ 2 *
          ∫ z : ℂ, (|‖1 + p.eval z‖ - 1|) ^ 2 * Real.exp (-‖z‖ ^ 2) :=
  LocalFockSPR_of_small_norm_exists_phase p hsmall

end FockSPR

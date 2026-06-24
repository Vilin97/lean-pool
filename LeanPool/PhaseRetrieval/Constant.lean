/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
import LeanPool.PhaseRetrieval.Constant.Internal.Local

/-!
# Showcase

This file packages the local Fock-space argument in a paper-friendly form.

The key reduction is the centered decomposition

`p = (p - C (p.eval 0)) + C (p.eval 0)`,

which kills the constant term and lets the core theorem `LocalFockSPR_of_small_norm`
apply to the centered polynomial. The phase-aligned conclusion is then obtained
by the wrapper in `LocalHelpers.lean`.
-/

open FockSPR MeasureTheory Complex Real Polynomial

noncomputable section

namespace FockSPR

/-- The centered polynomial obtained by removing the constant term. -/
def centeredPolynomial (p : Polynomial ℂ) : Polynomial ℂ :=
  p - Polynomial.C (p.eval 0)

/-- The centered polynomial has zero constant term. -/
theorem centeredPolynomial_eval_zero (p : Polynomial ℂ) :
    (centeredPolynomial p).eval 0 = 0 := by simp [centeredPolynomial]

/-- The paper-friendly orthogonal reduction step: split off the constant term. -/
theorem orthogonalReduction (p : Polynomial ℂ) :
    p = centeredPolynomial p + Polynomial.C (p.eval 0) := by
  simp [centeredPolynomial, sub_add_cancel]

/-- The centered core estimate, stated as a reusable theorem for the paper. -/
theorem orthogonalReduction_core
    (p : Polynomial ℂ)
    (hp_real : Complex.im (p.eval 0) = 0)
    (hsmall :
      (1 / Real.pi) * ∫ z : ℂ, ‖p.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ≤
        (1 / 4601 : ℝ) ^ 2) :
    ∫ z : ℂ, ‖p.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ≤
      23003 ^ 2 *
        ∫ z : ℂ, (|‖1 + p.eval z‖ - 1|) ^ 2 * Real.exp (-‖z‖ ^ 2) :=
  LocalFockSPR_of_small_norm p hp_real hsmall

/-- The phase-aligned version used in the final statement. -/
theorem orthogonalReduction_exists_phase
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

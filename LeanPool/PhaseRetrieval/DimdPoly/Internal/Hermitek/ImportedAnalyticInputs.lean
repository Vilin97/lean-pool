/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
/-
  # ImportedAnalyticInputs.lean
  Re-exported analytic inputs reused from the existing formalizations.

  Scaffolding notes:
  - `Imported/analytic_inputs.md`
-/
import LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermitek.TrueLevelBasis
import LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite.ImportedAnalyticInputs

/-! # ImportedAnalyticInputs -/


open Complex MeasureTheory Real Finset
open scoped BigOperators

noncomputable section

namespace HermitekLEAN

/-- Imported local circle estimate for positive frequencies. -/
theorem local_circle_estimate
    (E : Finset ℕ)
    (hpos : ∀ n ∈ E, 1 ≤ n)
    (c : ℕ → ℂ) :
    circleL2Sq (positiveTrigonometricPolynomial E c)
      ≤ 144 * E.card * circleRhoNormSq (positiveTrigonometricPolynomial E c) := by
  simpa [circleL2Sq, circleRhoNormSq, positiveTrigonometricPolynomial] using
    HermiteLEAN.local_circle_estimate E hpos c

/-- Imported high-frequency circle estimate. -/
theorem high_frequency_circle_estimate
    (N L : ℕ)
    (hN : 1 ≤ N)
    (hL : 1 ≤ L)
    (c : ℕ → ℂ)
    (hband : 1343 * (L : ℝ) ^ 2 ≤ (N : ℝ) ^ 2) :
    circleL2Sq (positiveTrigonometricPolynomial (frequencyBand N L) c)
      ≤ 32 * circleRhoNormSq (positiveTrigonometricPolynomial (frequencyBand N L) c) := by
  simpa [circleL2Sq, circleRhoNormSq, positiveTrigonometricPolynomial, frequencyBand] using
    HermiteLEAN.high_frequency_circle_estimate N L hN hL c hband

/-- Imported phase-normalized orthogonal reduction. -/
theorem phase_normalized_orthogonal_reduction
    {H : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (defect : H → ℝ)
    (hdefect_nonneg : ∀ h : H, 0 ≤ defect h)
    (f0 : H)
    (hf0 : ‖f0‖ = 1)
    (C : ℝ)
    (hC : 0 < C)
    (horth : ∀ g : H, inner ℂ g f0 = (0 : ℂ) → ‖g‖ ≤ C * defect g)
    (hscalar :
      ∀ h : H, (inner ℂ h f0).im = 0 →
        |(2 : ℝ) * (inner ℂ h f0).re + ‖h‖ ^ 2| ≤ defect h * (2 + ‖h‖))
    (hcompare :
      ∀ h : H, ∀ a : ℝ, defect (h - (a : ℂ) • f0) ≤ |a| + defect h) :
    ∃ δ Mloc : ℝ, 0 < δ ∧ 0 < Mloc ∧
      ∀ h : H, ‖h‖ ≤ δ → (inner ℂ h f0).im = 0 → ‖h‖ ≤ Mloc * defect h := by
  simpa using
    HermiteLEAN.phase_normalized_orthogonal_reduction
      defect hdefect_nonneg f0 hf0 C hC horth hscalar hcompare

end HermitekLEAN

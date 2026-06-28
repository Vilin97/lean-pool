/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Linarith
import LeanPool.OrdvecFormalization.QuotientKernel

/-!
# Score margins and quotient admission

This file avoids any claim that training implies quotient invariance.  Instead
it proves a sufficient condition: if a quotient score is uniformly close to a
full score and every full-score decision margin is larger than the error, then
threshold admission is unchanged.  If the quotient score factors through an
image quotient, the full threshold decision factors through it as well.
-/

open scoped NNReal

namespace OrdvecFormalization

/-- A two-sided uniform score approximation bound. -/
def ScoresWithin {Ω : Type} (full approx : Ω → ℝ) (ε : ℝ≥0) : Prop :=
  ∀ ω, full ω - (ε : ℝ) ≤ approx ω ∧ approx ω ≤ full ω + (ε : ℝ)

/-- Full-score threshold margins are separated from the cutoff by `ε`. -/
def ThresholdMargin {Ω : Type} (full : Ω → ℝ) (τ : ℝ) (ε : ℝ≥0) : Prop :=
  ∀ ω, τ + (ε : ℝ) < full ω ∨ full ω + (ε : ℝ) < τ

/-- Boolean threshold admission for a real-valued score. -/
noncomputable def thresholdAdmitBool {Ω : Type} (score : Ω → ℝ) (τ : ℝ) : Ω → Bool :=
  fun ω => if τ ≤ score ω then true else false

/--
A close approximate score with sufficient full-score margins gives the same
threshold decisions.
-/
theorem threshold_admit_iff_of_scoresWithin_and_margin {Ω : Type}
    (full approx : Ω → ℝ) (τ : ℝ) (ε : ℝ≥0)
    (hclose : ScoresWithin full approx ε)
    (hmargin : ThresholdMargin full τ ε) :
    ∀ ω, (τ ≤ full ω ↔ τ ≤ approx ω) := by
  intro ω
  rcases hclose ω with ⟨hlower, hupper⟩
  rcases hmargin ω with hpos | hneg
  · constructor
    · intro _hfull
      linarith
    · intro _happrox
      linarith
  · constructor
    · intro hfull
      linarith
    · intro happ
      linarith

/-- The Boolean threshold rule is unchanged under a close score with sufficient margins. -/
theorem thresholdAdmitBool_eq_of_scoresWithin_and_margin {Ω : Type}
    (full approx : Ω → ℝ) (τ : ℝ) (ε : ℝ≥0)
    (hclose : ScoresWithin full approx ε)
    (hmargin : ThresholdMargin full τ ε) :
    thresholdAdmitBool full τ = thresholdAdmitBool approx τ := by
  ext ω
  simp [thresholdAdmitBool,
    (threshold_admit_iff_of_scoresWithin_and_margin full approx τ ε hclose hmargin ω)]

/-- Thresholding a quotient-factorized score gives a quotient-factorized Boolean rule. -/
theorem thresholdAdmitBool_factorsThrough_of_score_factorsThrough {Ω Z : Type}
    (C : Ω → Z) (score : Ω → ℝ) (τ : ℝ)
    (hscore : RuleFactorsThrough C score) :
    RuleFactorsThrough C (thresholdAdmitBool score τ) := by
  rcases hscore with ⟨scoreq, hscoreq⟩
  refine ⟨fun z => if τ ≤ scoreq z then true else false, ?_⟩
  intro ω
  simp [thresholdAdmitBool, hscoreq ω]

/--
If a quotient score factors through the image quotient and is margin-stable
against the full score, then the full-score threshold admission rule factors
through the same image quotient.
-/
theorem thresholdAdmitBool_factorsThrough_image_of_score_margin {Ω Z : Type}
    [Fintype Ω] [DecidableEq Z]
    (C : Ω → Z) (full approx : Ω → ℝ) (τ : ℝ) (ε : ℝ≥0)
    (happrox : RuleFactorsThrough (imageQuotient C) approx)
    (hclose : ScoresWithin full approx ε)
    (hmargin : ThresholdMargin full τ ε) :
    RuleFactorsThrough (imageQuotient C) (thresholdAdmitBool full τ) := by
  rw [thresholdAdmitBool_eq_of_scoresWithin_and_margin full approx τ ε hclose hmargin]
  exact thresholdAdmitBool_factorsThrough_of_score_factorsThrough
    (imageQuotient C) approx τ happrox

end OrdvecFormalization

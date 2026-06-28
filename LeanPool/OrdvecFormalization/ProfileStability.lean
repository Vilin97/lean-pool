/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import LeanPool.OrdvecFormalization.ScoreMarginQuotient

/-!
# Profile stability

This file packages the finite score-level assumptions suggested by an encoder
distortion profile and a quotient geometry profile.  These profiles are formal
certificates inside the finite model: they do not assert that an empirical
encoder globally satisfies any metric bound.
-/

namespace OrdvecFormalization

open scoped NNReal

/--
A formal encoder-distortion certificate: the encoder score is uniformly close
to the source/task score at error `ε`.
-/
structure EncoderDistortionProfile {Ω : Type}
    (sourceScore encoderScore : Ω → ℝ) (ε : ℝ≥0) : Prop where
  scores_within : ScoresWithin sourceScore encoderScore ε

/--
A formal quotient-geometry certificate: the quotient score factors through the
reachable image quotient and uniformly approximates the encoder score.
-/
structure QuotientGeometryProfile {Ω Z : Type} [Fintype Ω] [DecidableEq Z]
    (C : Ω → Z) (encoderScore quotientScore : Ω → ℝ) (ε : ℝ≥0) : Prop where
  quotient_score : RuleFactorsThrough (imageQuotient C) quotientScore
  scores_within : ScoresWithin encoderScore quotientScore ε

/-- Uniform score-error bounds compose additively. -/
theorem scoresWithin_trans_add {Ω : Type}
    (sourceScore midScore approxScore : Ω → ℝ) (ε₁ ε₂ : ℝ≥0)
    (h₁ : ScoresWithin sourceScore midScore ε₁)
    (h₂ : ScoresWithin midScore approxScore ε₂) :
    ScoresWithin sourceScore approxScore (ε₁ + ε₂) := by
  intro ω
  rcases h₁ ω with ⟨h₁lower, h₁upper⟩
  rcases h₂ ω with ⟨h₂lower, h₂upper⟩
  constructor
  · rw [NNReal.coe_add]
    linarith
  · rw [NNReal.coe_add]
    linarith

/--
An encoder-distortion profile plus a quotient-geometry profile gives a single
source-to-quotient score bound.
-/
theorem scoresWithin_of_encoderDistortionProfile_and_quotientGeometryProfile
    {Ω Z : Type} [Fintype Ω] [DecidableEq Z]
    (C : Ω → Z)
    (sourceScore encoderScore quotientScore : Ω → ℝ)
    (εenc εquot : ℝ≥0)
    (henc : EncoderDistortionProfile sourceScore encoderScore εenc)
    (hquot :
      QuotientGeometryProfile C encoderScore quotientScore εquot) :
    ScoresWithin sourceScore quotientScore (εenc + εquot) :=
  scoresWithin_trans_add sourceScore encoderScore quotientScore εenc εquot
    henc.scores_within hquot.scores_within

/--
If the composed profile error is smaller than every source-score decision
margin, threshold admission is unchanged by the quotient score.
-/
theorem thresholdAdmitBool_eq_of_distortion_and_quotientGeometry
    {Ω Z : Type} [Fintype Ω] [DecidableEq Z]
    (C : Ω → Z)
    (sourceScore encoderScore quotientScore : Ω → ℝ)
    (τ : ℝ) (εenc εquot : ℝ≥0)
    (henc : EncoderDistortionProfile sourceScore encoderScore εenc)
    (hquot :
      QuotientGeometryProfile C encoderScore quotientScore εquot)
    (hmargin : ThresholdMargin sourceScore τ (εenc + εquot)) :
    thresholdAdmitBool sourceScore τ = thresholdAdmitBool quotientScore τ :=
  thresholdAdmitBool_eq_of_scoresWithin_and_margin
    sourceScore quotientScore τ (εenc + εquot)
    (scoresWithin_of_encoderDistortionProfile_and_quotientGeometryProfile
      C sourceScore encoderScore quotientScore εenc εquot henc hquot)
    hmargin

/--
If a quotient-geometry score is close enough after encoder distortion, the
source-score threshold rule factors through the reachable quotient image.
-/
theorem thresholdAdmitBool_factorsThrough_image_of_distortion_and_quotientGeometry
    {Ω Z : Type} [Fintype Ω] [DecidableEq Z]
    (C : Ω → Z)
    (sourceScore encoderScore quotientScore : Ω → ℝ)
    (τ : ℝ) (εenc εquot : ℝ≥0)
    (henc : EncoderDistortionProfile sourceScore encoderScore εenc)
    (hquot :
      QuotientGeometryProfile C encoderScore quotientScore εquot)
    (hmargin : ThresholdMargin sourceScore τ (εenc + εquot)) :
    RuleFactorsThrough (imageQuotient C) (thresholdAdmitBool sourceScore τ) :=
  thresholdAdmitBool_factorsThrough_image_of_score_margin
    C sourceScore quotientScore τ (εenc + εquot)
    hquot.quotient_score
    (scoresWithin_of_encoderDistortionProfile_and_quotientGeometryProfile
      C sourceScore encoderScore quotientScore εenc εquot henc hquot)
    hmargin

/--
The composed profile assumptions give kernel containment for the source-score
admission rule: every compression collision has the same threshold decision.
-/
theorem kernelContainedInTarget_of_distortion_and_quotientGeometry
    {Ω Z : Type} [Fintype Ω] [DecidableEq Z]
    (C : Ω → Z)
    (sourceScore encoderScore quotientScore : Ω → ℝ)
    (τ : ℝ) (εenc εquot : ℝ≥0)
    (henc : EncoderDistortionProfile sourceScore encoderScore εenc)
    (hquot :
      QuotientGeometryProfile C encoderScore quotientScore εquot)
    (hmargin : ThresholdMargin sourceScore τ (εenc + εquot)) :
    KernelContainedInTarget C (thresholdAdmitBool sourceScore τ) :=
  kernelContainedInTarget_of_ruleFactorsThrough_image C
    (thresholdAdmitBool sourceScore τ)
    (thresholdAdmitBool_factorsThrough_image_of_distortion_and_quotientGeometry
      C sourceScore encoderScore quotientScore τ εenc εquot henc hquot
      hmargin)

end OrdvecFormalization

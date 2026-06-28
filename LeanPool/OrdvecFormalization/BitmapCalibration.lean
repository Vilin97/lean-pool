/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import LeanPool.OrdvecFormalization.CalibratedEvidence
import LeanPool.OrdvecFormalization.BitmapIncidence
import LeanPool.OrdvecFormalization.OverlapBayesOptimal
import LeanPool.OrdvecFormalization.BitmapNull

/-!
# Constant-weight bitmap overlap thresholds

This file connects the canonical overlap-tilt theorem to the exact
constant-weight bitmap null.  The canonical signal theorem supplies a
Bayes-optimal actual-overlap cutoff; the bitmap null theorem identifies the
same numeric cutoff with a hypergeometric upper-tail probability under the
uniform `K`-active bitmap law.

Main definitions:
- `ConstantWeightBitmap`: the subtype of `K`-active bitmaps.
- `constantWeightBitmapOverlapEvidence`: literal bitmap overlap as feasible overlap
  evidence.
- `constantWeightBitmapUniformLaw`: the uniform finite law over `K`-active bitmap
  elements.

Main statements:
- `exists_constantWeightBitmapOverlapTail_finiteBayesRisk_le_and_hypergeomTail`:
  arbitrary positive-base canonical signal model, with uniform-null tail
  calibration at the same cutoff.
- `exists_uniformBitmapOverlapTail_finiteBayesRisk_le_and_hypergeomTail`:
  uniform-base, zero-null-tilt specialization where the model null is the
  uniform bitmap null.

-/

open scoped NNReal ENNReal

namespace OrdvecFormalization

/--
Uniform constant-weight bitmap overlap tails as a supplied ordered calibration.

This record packages the exact hypergeometric upper-tail equality proved in
`BitmapNull`; it does not by itself identify the event with any full-space
decision rule.
-/
noncomputable def constantWeightBitmapOverlapTailCalibration {D K : ℕ} (hK : K ≤ D)
    {q : Finset (BitmapCoord D)} (hq : q.card = K) :
    OrderedTailCalibration
      ((bitmapOverlapParams D K hK).hi - (bitmapOverlapParams D K hK).lo)
      (Finset (BitmapCoord D)) where
  event cut :=
    (bitmapOverlapTailEvent D K ((bitmapOverlapParams D K hK).lo + cut.val) q :
      Set (Finset (BitmapCoord D)))
  mass event := (bitmapUniformPMF D K hK).toOuterMeasure event
  value cut :=
    (bitmapHypergeomTail D K ((bitmapOverlapParams D K hK).lo + cut.val) : ℝ≥0∞)
  calibrated cut := by
    exact bitmapUniformPMF_overlapTail_prob (D := D) (K := K)
      (t := (bitmapOverlapParams D K hK).lo + cut.val) hK (q := q) hq

/--
Finite Bayes-risk theorem with exact bitmap-null calibration.

For a canonical overlap tilt on the feasible overlap support of two `K`-active
bitmaps, the produced Bayes-optimal threshold has a hypergeometric upper-tail
probability under the uniform bitmap null at the same actual-overlap cutoff.
-/
theorem exists_overlapQuotientThreshold_finiteBayesRisk_le_and_bitmapHypergeomTail
    {Ω Ωq : Type} [Fintype Ω] {D K : ℕ} (hK : K ≤ D)
    (base : FiniteLaw Ω) (Q : Ω → Ωq)
    (O : Ωq → (bitmapOverlapParams D K hK).support)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ < θ₁) (prior : Prior) (hprior : 0 < prior.prob)
    {q : Finset (BitmapCoord D)} (hq : q.card = K) :
    ∃ cut : Fin ((bitmapOverlapParams D K hK).hi - (bitmapOverlapParams D K hK).lo + 2),
      (∀ R : Set Ω,
        finiteBayesRisk
            (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
            (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
            prior (overlapQuotientThresholdSet (bitmapOverlapParams D K hK) Q O cut) ≤
          finiteBayesRisk
            (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
            (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
            prior R) ∧
      (bitmapUniformPMF D K hK).toOuterMeasure
          (bitmapOverlapTailEvent D K ((bitmapOverlapParams D K hK).lo + cut.val) q :
            Set (Finset (BitmapCoord D))) =
        (bitmapHypergeomTail D K ((bitmapOverlapParams D K hK).lo + cut.val) : ℝ≥0∞) := by
  let p : FNCHParams := bitmapOverlapParams D K hK
  rcases
    exists_calibratedOrderedThreshold_finiteBayesRisk_le_of_orderedEvidenceFactor
      Q O
      (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
      (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
      prior hprior (constantWeightBitmapOverlapTailCalibration hK hq)
      (finiteExponentialTilt_likelihoodRatioFactorsThroughOrderedEvidence base Q O hθ.le)
      with ⟨cut, hopt, hcal⟩
  refine ⟨cut, ?_, ?_⟩
  · intro R
    simpa [p, overlapQuotientThresholdSet_eq_orderedQuotientThresholdSet p Q O cut]
      using hopt R
  · simpa [constantWeightBitmapOverlapTailCalibration, p] using hcal

/--
Constant-weight bitmap specialization of the finite Bayes-risk theorem.

Here the full observation space is the finite type of `K`-active bitmaps, and
the evidence statistic is literal bitmap overlap. The Bayes-optimal canonical
tilt rule is exactly the bitmap overlap tail event whose null probability is the
hypergeometric upper tail.
-/
theorem exists_constantWeightBitmapOverlapTail_finiteBayesRisk_le_and_hypergeomTail
    {D K : ℕ} (hK : K ≤ D) {q : Finset (BitmapCoord D)} (hq : q.card = K)
    (base : FiniteLaw (ConstantWeightBitmap D K))
    {θ₀ θ₁ : ℝ} (hθ : θ₀ < θ₁) (prior : Prior) (hprior : 0 < prior.prob) :
    ∃ cut : Fin ((bitmapOverlapParams D K hK).hi - (bitmapOverlapParams D K hK).lo + 2),
      (∀ R : Set (ConstantWeightBitmap D K),
        finiteBayesRisk
            (finiteExponentialTilt base (constantWeightBitmapOverlapEvidence hK hq) θ₀)
            (finiteExponentialTilt base (constantWeightBitmapOverlapEvidence hK hq) θ₁)
            prior
            (constantWeightBitmapOverlapTailSet D K ((bitmapOverlapParams D K hK).lo + cut.val) q) ≤
          finiteBayesRisk
            (finiteExponentialTilt base (constantWeightBitmapOverlapEvidence hK hq) θ₀)
            (finiteExponentialTilt base (constantWeightBitmapOverlapEvidence hK hq) θ₁)
            prior R) ∧
      (bitmapUniformPMF D K hK).toOuterMeasure
          (bitmapOverlapTailEvent D K ((bitmapOverlapParams D K hK).lo + cut.val) q :
            Set (Finset (BitmapCoord D))) =
        (bitmapHypergeomTail D K ((bitmapOverlapParams D K hK).lo + cut.val) : ℝ≥0∞) := by
  let p : FNCHParams := bitmapOverlapParams D K hK
  let O := constantWeightBitmapOverlapEvidence hK hq
  rcases
    exists_calibratedOrderedThreshold_finiteBayesRisk_le_of_orderedEvidenceFactor
      (fun d : ConstantWeightBitmap D K => d) O
      (finiteExponentialTilt base O θ₀)
      (finiteExponentialTilt base O θ₁)
      prior hprior (constantWeightBitmapOverlapTailCalibration hK hq)
      (finiteExponentialTilt_likelihoodRatioFactorsThroughOrderedEvidence base
        (fun d : ConstantWeightBitmap D K => d) O hθ.le)
      with ⟨cut, hopt, hcal⟩
  refine ⟨cut, ?_, ?_⟩
  · intro R
    have hevent :
        overlapQuotientThresholdSet p (fun d : ConstantWeightBitmap D K => d) O cut =
          constantWeightBitmapOverlapTailSet D K (p.lo + cut.val) q := by
      simpa [p, O] using
        (overlapQuotientThresholdSet_constantWeightBitmapOverlapEvidence_eq hK hq cut)
    simpa [p, O, ← overlapQuotientThresholdSet_eq_orderedQuotientThresholdSet p
      (fun d : ConstantWeightBitmap D K => d) O cut, hevent] using hopt R
  · simpa [constantWeightBitmapOverlapTailCalibration, p] using hcal

/--
Cost-sensitive theorem with exact bitmap-null calibration.

The asymmetric-cost version has the same form: priors and costs select a
Bayes-optimal cutoff, and the bitmap null gives the exact hypergeometric tail
mass at that cutoff.
-/
theorem exists_overlapQuotientThreshold_finiteCostedBayesRisk_le_and_bitmapHypergeomTail
    {Ω Ωq : Type} [Fintype Ω] {D K : ℕ} (hK : K ≤ D)
    (base : FiniteLaw Ω) (Q : Ω → Ωq)
    (O : Ωq → (bitmapOverlapParams D K hK).support)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ < θ₁) (prior : Prior) (costs : DecisionCosts)
    (hw1 : 0 < costs.falseReject * prior.prob)
    {q : Finset (BitmapCoord D)} (hq : q.card = K) :
    ∃ cut : Fin ((bitmapOverlapParams D K hK).hi - (bitmapOverlapParams D K hK).lo + 2),
      (∀ R : Set Ω,
        finiteCostedBayesRisk
            (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
            (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
            prior costs
            (overlapQuotientThresholdSet (bitmapOverlapParams D K hK) Q O cut) ≤
          finiteCostedBayesRisk
            (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
            (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
            prior costs R) ∧
      (bitmapUniformPMF D K hK).toOuterMeasure
          (bitmapOverlapTailEvent D K ((bitmapOverlapParams D K hK).lo + cut.val) q :
            Set (Finset (BitmapCoord D))) =
        (bitmapHypergeomTail D K ((bitmapOverlapParams D K hK).lo + cut.val) : ℝ≥0∞) := by
  let p : FNCHParams := bitmapOverlapParams D K hK
  rcases
    exists_calibratedOrderedThreshold_finiteCostedBayesRisk_le_of_orderedEvidenceFactor
      Q O
      (finiteExponentialTilt base (fun ω => O (Q ω)) θ₀)
      (finiteExponentialTilt base (fun ω => O (Q ω)) θ₁)
      prior costs hw1 (constantWeightBitmapOverlapTailCalibration hK hq)
      (finiteExponentialTilt_likelihoodRatioFactorsThroughOrderedEvidence base Q O hθ.le)
      with ⟨cut, hopt, hcal⟩
  refine ⟨cut, ?_, ?_⟩
  · intro R
    simpa [p, overlapQuotientThresholdSet_eq_orderedQuotientThresholdSet p Q O cut]
      using hopt R
  · simpa [constantWeightBitmapOverlapTailCalibration, p] using hcal

/-- Cost-sensitive constant-weight bitmap specialization. -/
theorem exists_constantWeightBitmapOverlapTail_finiteCostedBayesRisk_le_and_hypergeomTail
    {D K : ℕ} (hK : K ≤ D) {q : Finset (BitmapCoord D)} (hq : q.card = K)
    (base : FiniteLaw (ConstantWeightBitmap D K))
    {θ₀ θ₁ : ℝ} (hθ : θ₀ < θ₁) (prior : Prior) (costs : DecisionCosts)
    (hw1 : 0 < costs.falseReject * prior.prob) :
    ∃ cut : Fin ((bitmapOverlapParams D K hK).hi - (bitmapOverlapParams D K hK).lo + 2),
      (∀ R : Set (ConstantWeightBitmap D K),
        finiteCostedBayesRisk
            (finiteExponentialTilt base (constantWeightBitmapOverlapEvidence hK hq) θ₀)
            (finiteExponentialTilt base (constantWeightBitmapOverlapEvidence hK hq) θ₁)
            prior costs
            (constantWeightBitmapOverlapTailSet D K ((bitmapOverlapParams D K hK).lo + cut.val) q) ≤
          finiteCostedBayesRisk
            (finiteExponentialTilt base (constantWeightBitmapOverlapEvidence hK hq) θ₀)
            (finiteExponentialTilt base (constantWeightBitmapOverlapEvidence hK hq) θ₁)
            prior costs R) ∧
      (bitmapUniformPMF D K hK).toOuterMeasure
          (bitmapOverlapTailEvent D K ((bitmapOverlapParams D K hK).lo + cut.val) q :
            Set (Finset (BitmapCoord D))) =
        (bitmapHypergeomTail D K ((bitmapOverlapParams D K hK).lo + cut.val) : ℝ≥0∞) := by
  let p : FNCHParams := bitmapOverlapParams D K hK
  let O := constantWeightBitmapOverlapEvidence hK hq
  rcases
    exists_calibratedOrderedThreshold_finiteCostedBayesRisk_le_of_orderedEvidenceFactor
      (fun d : ConstantWeightBitmap D K => d) O
      (finiteExponentialTilt base O θ₀)
      (finiteExponentialTilt base O θ₁)
      prior costs hw1 (constantWeightBitmapOverlapTailCalibration hK hq)
      (finiteExponentialTilt_likelihoodRatioFactorsThroughOrderedEvidence base
        (fun d : ConstantWeightBitmap D K => d) O hθ.le)
      with ⟨cut, hopt, hcal⟩
  refine ⟨cut, ?_, ?_⟩
  · intro R
    have hevent :
        overlapQuotientThresholdSet p (fun d : ConstantWeightBitmap D K => d) O cut =
          constantWeightBitmapOverlapTailSet D K (p.lo + cut.val) q := by
      simpa [p, O] using
        (overlapQuotientThresholdSet_constantWeightBitmapOverlapEvidence_eq hK hq cut)
    simpa [p, O, ← overlapQuotientThresholdSet_eq_orderedQuotientThresholdSet p
      (fun d : ConstantWeightBitmap D K => d) O cut, hevent] using hopt R
  · simpa [constantWeightBitmapOverlapTailCalibration, p] using hcal

/--
Uniform-null specialization of the bitmap theorem.

Here the base law is uniform over `K`-active bitmaps and the null signal
parameter is `0`, so the negative-class model is the zero-tilt of the uniform
bitmap law.
-/
theorem exists_uniformBitmapOverlapTail_finiteBayesRisk_le_and_hypergeomTail
    {D K : ℕ} (hK : K ≤ D) {q : Finset (BitmapCoord D)} (hq : q.card = K)
    {θ : ℝ} (hθ : 0 < θ) (prior : Prior) (hprior : 0 < prior.prob) :
    ∃ cut : BitmapCut D K hK,
      (∀ R : Set (ConstantWeightBitmap D K),
        finiteBayesRisk
            (finiteExponentialTilt (constantWeightBitmapUniformLaw D K hK)
              (constantWeightBitmapOverlapEvidence hK hq) 0)
            (finiteExponentialTilt (constantWeightBitmapUniformLaw D K hK)
              (constantWeightBitmapOverlapEvidence hK hq) θ)
            prior
            (constantWeightBitmapOverlapTailSet D K (bitmapCutThreshold hK cut) q) ≤
          finiteBayesRisk
            (finiteExponentialTilt (constantWeightBitmapUniformLaw D K hK)
              (constantWeightBitmapOverlapEvidence hK hq) 0)
            (finiteExponentialTilt (constantWeightBitmapUniformLaw D K hK)
              (constantWeightBitmapOverlapEvidence hK hq) θ)
            prior R) ∧
      (bitmapUniformPMF D K hK).toOuterMeasure
          (bitmapOverlapTailEvent D K (bitmapCutThreshold hK cut) q :
            Set (Finset (BitmapCoord D))) =
        (bitmapHypergeomTail D K (bitmapCutThreshold hK cut) : ℝ≥0∞) := by
  simpa [BitmapCut, bitmapCutThreshold, bitmapOverlapParams] using
    (exists_constantWeightBitmapOverlapTail_finiteBayesRisk_le_and_hypergeomTail
      hK hq (constantWeightBitmapUniformLaw D K hK)
      hθ prior hprior)

/-- Short alias for the headline uniform bitmap overlap theorem. -/
theorem uniformBitmapOverlapTailOptimal
    {D K : ℕ} (hK : K ≤ D) {q : Finset (BitmapCoord D)} (hq : q.card = K)
    {θ : ℝ} (hθ : 0 < θ) (prior : Prior) (hprior : 0 < prior.prob) :
    ∃ cut : BitmapCut D K hK,
      (∀ R : Set (ConstantWeightBitmap D K),
        finiteBayesRisk
            (finiteExponentialTilt (constantWeightBitmapUniformLaw D K hK)
              (constantWeightBitmapOverlapEvidence hK hq) 0)
            (finiteExponentialTilt (constantWeightBitmapUniformLaw D K hK)
              (constantWeightBitmapOverlapEvidence hK hq) θ)
            prior
            (constantWeightBitmapOverlapTailSet D K (bitmapCutThreshold hK cut) q) ≤
          finiteBayesRisk
            (finiteExponentialTilt (constantWeightBitmapUniformLaw D K hK)
              (constantWeightBitmapOverlapEvidence hK hq) 0)
            (finiteExponentialTilt (constantWeightBitmapUniformLaw D K hK)
              (constantWeightBitmapOverlapEvidence hK hq) θ)
            prior R) ∧
      (bitmapUniformPMF D K hK).toOuterMeasure
          (bitmapOverlapTailEvent D K (bitmapCutThreshold hK cut) q :
            Set (Finset (BitmapCoord D))) =
        (bitmapHypergeomTail D K (bitmapCutThreshold hK cut) : ℝ≥0∞) :=
  exists_uniformBitmapOverlapTail_finiteBayesRisk_le_and_hypergeomTail hK hq hθ prior hprior

/-- Cost-sensitive uniform-null specialization of the bitmap theorem. -/
theorem exists_uniformBitmapOverlapTail_finiteCostedBayesRisk_le_and_hypergeomTail
    {D K : ℕ} (hK : K ≤ D) {q : Finset (BitmapCoord D)} (hq : q.card = K)
    {θ : ℝ} (hθ : 0 < θ) (prior : Prior) (costs : DecisionCosts)
    (hw1 : 0 < costs.falseReject * prior.prob) :
    ∃ cut : BitmapCut D K hK,
      (∀ R : Set (ConstantWeightBitmap D K),
        finiteCostedBayesRisk
            (finiteExponentialTilt (constantWeightBitmapUniformLaw D K hK)
              (constantWeightBitmapOverlapEvidence hK hq) 0)
            (finiteExponentialTilt (constantWeightBitmapUniformLaw D K hK)
              (constantWeightBitmapOverlapEvidence hK hq) θ)
            prior costs
            (constantWeightBitmapOverlapTailSet D K (bitmapCutThreshold hK cut) q) ≤
          finiteCostedBayesRisk
            (finiteExponentialTilt (constantWeightBitmapUniformLaw D K hK)
              (constantWeightBitmapOverlapEvidence hK hq) 0)
            (finiteExponentialTilt (constantWeightBitmapUniformLaw D K hK)
              (constantWeightBitmapOverlapEvidence hK hq) θ)
            prior costs R) ∧
      (bitmapUniformPMF D K hK).toOuterMeasure
          (bitmapOverlapTailEvent D K (bitmapCutThreshold hK cut) q :
            Set (Finset (BitmapCoord D))) =
        (bitmapHypergeomTail D K (bitmapCutThreshold hK cut) : ℝ≥0∞) := by
  simpa [BitmapCut, bitmapCutThreshold, bitmapOverlapParams] using
    (exists_constantWeightBitmapOverlapTail_finiteCostedBayesRisk_le_and_hypergeomTail
      hK hq (constantWeightBitmapUniformLaw D K hK)
      hθ prior costs hw1)

end OrdvecFormalization

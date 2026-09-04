/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import LeanPool.EhrhartVolumeInequality.Resolvent
import all LeanPool.EhrhartVolumeInequality.Resolvent
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.Probability.Moments.Variance

/-!
# Ehrhart volume inequality: Convexity

Physical-measure, convexity, and probability-transfer arguments.
-/

noncomputable local instance {n : ℕ} :
    CoeFun (ContDiffBump (0 : Fin n → ℝ)) (fun _ => (Fin n → ℝ) → ℝ) :=
  ⟨ContDiffBump.toFun⟩

noncomputable section

namespace Ehrhart

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace BergmanJetHolomorphicPhysicalMeasure

open Set Function Filter MeasureTheory Metric Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence MatrixTorusBochnerBridge
open MomentOptimizer MomentTargetGeodesic MomentFirstVariation MomentMoserTrudinger
open BergmanJetEnvelopePlurisubharmonic BergmanJetJointHolomorphicClosure
open BergmanJetJointHolomorphicPlurisubharmonicSmoothing BergmanJetStrictRadialRegularizer
open BergmanJetJointHolomorphicStrictSchur JetEnvelopeGlobalPlurisubharmonic
open JetEnvelopeRightDerivative JetEnvelopeTrueRadialMollifier EnvelopeSmoothing
open EnvelopeGeneralTorusDescent RadialPartitionBounds LogPartitionConvexity WeightedTorusDolbeault
open ArbitraryBodyOneSidedAngularResolventDefect
open scoped BigOperators ENNReal Topology ContDiff Convolution

private def momentWeakHolomorphicJointMollifierLowerBound
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (q : SourceJointComplexCover n) : ℝ :=
  momentJointGlobalLowerBound K F -
    BodyScale.canonicalScale K *
      (|sourceJointCoverTime q| + ‖sourceJointRealTimeCLM n‖)

private theorem momentWeakHolomorphicJointMollifierLowerBound_le_mollification
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    (q : SourceJointComplexCover n) :
    momentWeakHolomorphicJointMollifierLowerBound K F q ≤
      momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k q := by
  let C : ℝ :=
    momentWeakHolomorphicJointMollifierLowerBound K F q
  have hleft : Integrable
      (fun y : SourceJointComplexCover n =>
        sourceJointTrueRadialMollifier n k y * C)
      (volume : Measure (SourceJointComplexCover n)) :=
    (integrable_sourceJointTrueRadialMollifier n k).mul_const C
  have hright : Integrable
      (fun y : SourceJointComplexCover n =>
        sourceJointTrueRadialMollifier n k y *
          momentWeakJointCoverUpperEnvelope
            K F htransport p (q - y))
      (volume : Measure (SourceJointComplexCover n)) :=
    integrable_sourceJointTrueRadialMollifier_mul_translate
      (locallyIntegrable_momentWeakJointCoverUpperEnvelope
        K F htransport p) k q
  change C ≤ _
  unfold momentWeakHolomorphicJointTrueRadialMollification
    sourceJointTrueRadialSmoothed
  rw [MeasureTheory.convolution_def]
  calc
    C = ∫ y : SourceJointComplexCover n,
        sourceJointTrueRadialMollifier n k y * C := by
          rw [MeasureTheory.integral_mul_const,
            integral_sourceJointTrueRadialMollifier, one_mul]
    _ ≤ ∫ y : SourceJointComplexCover n,
          sourceJointTrueRadialMollifier n k y *
            momentWeakJointCoverUpperEnvelope
              K F htransport p (q - y) := by
      apply MeasureTheory.integral_mono hleft hright
      intro y
      by_cases hy : sourceJointTrueRadialMollifier n k y = 0
      · simp only [hy, zero_mul, Std.le_refl]
      · apply mul_le_mul_of_nonneg_left _
          (sourceJointTrueRadialMollifier_nonneg n k y)
        have hball :=
          support_sourceJointTrueRadialMollifier_subset_closedBall k hy
        have hynorm : ‖y‖ ≤ (1 : ℝ) := by
          have hsmall :
              ‖y‖ ≤ 1 / ((k + 1 : ℕ) : ℝ) := by
            simpa only [Nat.cast_add, Nat.cast_one, one_div, mem_closedBall, dist_zero_right]
              using hball
          have hk : 0 < ((k + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.zero_lt_succ k
          have hradius : 1 / ((k + 1 : ℕ) : ℝ) ≤ 1 := by
            apply (div_le_iff₀ hk).mpr
            norm_num
          exact hsmall.trans hradius
        have htime :
            |sourceJointCoverTime (q - y)| ≤
              |sourceJointCoverTime q| +
                ‖sourceJointRealTimeCLM n‖ := by
          calc
            |sourceJointCoverTime (q - y)| ≤
                |sourceJointCoverTime q| +
                  ‖sourceJointRealTimeCLM n‖ * ‖y‖ :=
              abs_sourceJointCoverTime_sub_le q y
            _ ≤ |sourceJointCoverTime q| +
                ‖sourceJointRealTimeCLM n‖ := by
              exact add_le_add (le_refl _)
                (mul_le_of_le_one_right
                  (norm_nonneg (sourceJointRealTimeCLM n)) hynorm)
        have hmin :
            -(|sourceJointCoverTime q| +
                ‖sourceJointRealTimeCLM n‖) ≤
              min (sourceJointCoverTime (q - y)) 0 := by
          apply le_min
          · linarith [neg_abs_le (sourceJointCoverTime (q - y))]
          · have hn :
                0 ≤ |sourceJointCoverTime q| +
                  ‖sourceJointRealTimeCLM n‖ :=
                add_nonneg (abs_nonneg _) (norm_nonneg _)
            linarith
        calc
          C ≤ momentWeakJointCoverFiniteMinorant
              K F (q - y) := by
                dsimp [C,
                  momentWeakHolomorphicJointMollifierLowerBound,
                  momentWeakJointCoverFiniteMinorant]
                nlinarith [BodyScale.canonicalScale_pos K]
          _ ≤ momentWeakJointCoverUpperEnvelope
              K F htransport p (q - y) :=
            momentWeakJointCoverFiniteMinorant_le_upperEnvelope
              K F htransport p (q - y)

private def momentWeakHolomorphicJointTimeLowerBound
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K) (t : ℝ) : ℝ :=
  momentJointGlobalLowerBound K F -
    BodyScale.canonicalScale K *
      (|t| + ‖sourceJointRealTimeCLM n‖)

private theorem momentWeakHolomorphicJointTimeLowerBound_le_mollification
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) (k : ℕ) (t : ℝ) :
    momentWeakHolomorphicJointTimeLowerBound K F t ≤
      momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k (sourceJointTimeEmbedding z t) := by
  simpa only [momentWeakHolomorphicJointTimeLowerBound, tsub_le_iff_right,
    momentWeakHolomorphicJointMollifierLowerBound, sourceJointCoverTime_timeEmbedding] using
      momentWeakHolomorphicJointMollifierLowerBound_le_mollification
        K F htransport p k (sourceJointTimeEmbedding z t)

private theorem momentWeakHolomorphicStrictRadialPotential_norm_lower
    {n : ℕ} (K : CenteredBody n)
    (x : Space n) :
    momentBodyStrictScale K * ‖x‖ ≤
      momentBodyStrictRadialPotential K x := by
  calc
    momentBodyStrictScale K * ‖x‖ ≤
        momentBodyStrictScale K *
          (∑ i : Fin n, |x i|) := by
      exact mul_le_mul_of_nonneg_left
        (SupportFunction.norm_le_sum_abs x)
        (momentBodyStrictScale_pos K).le
    _ ≤ momentBodyStrictRadialPotential K x :=
      momentBodyStrictRadialPotential_sum_abs_lower K x

private theorem momentWeakHolomorphicStrictJointTorusWeight_norm_coercivity
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (t : ℝ)
    {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (q : LogTorus n) :
    (ε * momentBodyStrictScale K) * ‖q.1‖ +
        (1 - ε) * momentWeakHolomorphicJointTimeLowerBound K F t ≤
      momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k t q := by
  have hweak :=
    momentWeakHolomorphicJointTimeLowerBound_le_mollification
      K F htransport p (sourceTorusCoverPoint q) k t
  have hrad :=
    momentWeakHolomorphicStrictRadialPotential_norm_lower K q.1
  have hweak' := mul_le_mul_of_nonneg_left hweak
    (sub_nonneg.mpr hε₁)
  have hrad' := mul_le_mul_of_nonneg_left hrad hε₀
  rw [momentWeakHolomorphicStrictJointTorusWeight,
    jointSourceTorusWeight_eq_cover]
  unfold momentWeakHolomorphicStrictJointCoverWeight
  have href :
      matrixSourceCoverPotential
        (momentBodyStrictRadialPotential K)
        (sourceJointTimeEmbedding (sourceTorusCoverPoint q) t).1 =
        momentBodyStrictRadialPotential K q.1 := by
    simp only [sourceJointTimeEmbedding, sourceTorusCoverPoint,
      matrixSourceCoverPotential_logarithmicPoint]
  rw [href]
  nlinarith

private theorem integrable_exp_neg_momentWeakHolomorphicStrictJointTorusWeight
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (t : ℝ)
    {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) :
    Integrable
      (fun q : LogTorus n =>
        Real.exp
          (-momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t q))
      (sourceTorusBaseMeasure n) := by
  let δ : ℝ := ε * momentBodyStrictScale K
  let C : ℝ :=
    -(1 - ε) * momentWeakHolomorphicJointTimeLowerBound K F t
  have hδ : 0 < δ :=
    mul_pos hε₀ (momentBodyStrictScale_pos K)
  have hrad : Integrable
      (fun x : Space n => Real.exp (-δ * ‖x‖))
      (volume : Measure (Space n)) :=
    integrable_exp_neg_mul_norm_all hδ
  have hang : Integrable
      (fun _ : AngularTorus n => (1 : ℝ))
      (angularMeasure n) :=
    integrable_const 1
  have hprod : Integrable
      (fun q : LogTorus n =>
        Real.exp (-δ * ‖q.1‖) * (1 : ℝ))
      (sourceTorusBaseMeasure n) := by
    simpa only [neg_mul, mul_one, sourceTorusBaseMeasure] using hrad.mul_prod hang
  have hmajor := hprod.const_mul (Real.exp C)
  have hmeas : AEStronglyMeasurable
      (fun q : LogTorus n =>
        Real.exp
          (-momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t q))
      (sourceTorusBaseMeasure n) :=
    (Real.continuous_exp.comp
      (continuous_momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k t).neg).aestronglyMeasurable
  apply hmajor.mono' hmeas
  filter_upwards [] with q
  change
    ‖Real.exp
        (-momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k t q)‖ ≤
      Real.exp C * (Real.exp (-δ * ‖q.1‖) * (1 : ℝ))
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp only [mul_one]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hc :=
    momentWeakHolomorphicStrictJointTorusWeight_norm_coercivity
      K F htransport p k t hε₀.le hε₁ q
  dsimp [δ, C]
  linarith

private theorem momentWeakHolomorphicStrictJointWeightedMeasure_isFinite
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (t : ℝ)
    {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) :
    IsFiniteMeasure
      (angularWeightedTorusMeasure
        (momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k t)) := by
  apply angularWeightedTorusMeasure_isFinite_of_integrable
  exact integrable_exp_neg_momentWeakHolomorphicStrictJointTorusWeight
    K F htransport p k t hε₀ hε₁

private theorem momentWeakHolomorphicStrictJointPartition_pos
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (t : ℝ)
    {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) :
    0 < sourcePartition
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k) t := by
  exact angularWeightedTorusDensity_integral_pos
    (integrable_exp_neg_momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p k t hε₀ hε₁)

private theorem momentWeakHolomorphicStrictJointProbability_univ
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (t : ℝ)
    {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) :
    sourceProbability
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k) t Set.univ = 1 := by
  let a : ℝ → LogTorus n → ℝ :=
    momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p ε k
  have hpart : 0 < sourcePartition a t :=
    momentWeakHolomorphicStrictJointPartition_pos
      K F htransport p k t hε₀ hε₁
  have hraw : Integrable
      (sourceTimeDensity a t)
      (sourceTorusBaseMeasure n) :=
    integrable_exp_neg_momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p k t hε₀ hε₁
  have hnorm : Integrable
      (sourceNormalizedDensity a t)
      (sourceTorusBaseMeasure n) := by
    exact hraw.div_const _
  change sourceProbability a t Set.univ = 1
  unfold sourceProbability
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    hnorm
    (Filter.Eventually.of_forall fun q =>
      (div_pos (Real.exp_pos _) hpart).le)]
  change
    ENNReal.ofReal
      (∫ q : LogTorus n,
        sourceTimeDensity a t q / sourcePartition a t
          ∂(sourceTorusBaseMeasure n)) = 1
  rw [MeasureTheory.integral_div]
  change ENNReal.ofReal
    (sourcePartition a t / sourcePartition a t) = 1
  rw [div_self hpart.ne']
  exact ENNReal.ofReal_one

private theorem momentWeakHolomorphicStrictJointProbability_isProbability
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (t : ℝ)
    {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) :
    IsProbabilityMeasure
      (sourceProbability
        (momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k) t) :=
  ⟨momentWeakHolomorphicStrictJointProbability_univ
    K F htransport p k t hε₀ hε₁⟩

private theorem momentWeakHolomorphicStrictJointProbability_eq_smul_weighted
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (t : ℝ)
    {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) :
    sourceProbability
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k) t =
      (ENNReal.ofReal
        (sourcePartition
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k) t))⁻¹ •
        angularWeightedTorusMeasure
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t) := by
  let a : ℝ → LogTorus n → ℝ :=
    momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p ε k
  have hpart : 0 < sourcePartition a t :=
    momentWeakHolomorphicStrictJointPartition_pos
      K F htransport p k t hε₀ hε₁
  have hmeas : Measurable
      (fun q : LogTorus n =>
        ENNReal.ofReal (angularWeightedTorusDensity (a t) q)) :=
    ENNReal.measurable_ofReal.comp
      (continuous_angularWeightedTorusDensity
        (continuous_momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k t)).measurable
  change sourceProbability a t =
    (ENNReal.ofReal (sourcePartition a t))⁻¹ •
      angularWeightedTorusMeasure (a t)
  unfold sourceProbability angularWeightedTorusMeasure
  rw [← MeasureTheory.withDensity_smul _ hmeas]
  congr 1
  funext q
  change ENNReal.ofReal
    (Real.exp (-a t q) / sourcePartition a t) =
      (ENNReal.ofReal (sourcePartition a t))⁻¹ *
        ENNReal.ofReal (Real.exp (-a t q))
  rw [ENNReal.ofReal_div_of_pos hpart]
  simp only [div_eq_mul_inv, mul_comm]

end BergmanJetHolomorphicPhysicalMeasure

namespace BergmanJetJointHolomorphicPhysicalApproximation

open Set Function Filter MeasureTheory Metric
open TorusCharacters WeightedTorusHilbert MatrixTorusBochnerBridge MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation MomentMoserTrudinger BergmanJetTorusEnvelope
open BergmanJetTorusCoercivity BergmanJetStrictRadialRegularizer
open BergmanJetJointEnvelopeRegularization BergmanJetJointHolomorphicClosure
open BergmanJetJointHolomorphicPlurisubharmonicSmoothing BergmanJetJointHolomorphicStrictSchur
open BergmanJetJointHolomorphicApproximation BergmanJetHolomorphicPhysicalMeasure
open JetEnvelopeRightDerivative JetEnvelopeSlopeConvergence JetEnvelopeGlobalPlurisubharmonic
open EnvelopeSmoothing EnvelopeGeneralTorusDescent LogPartitionConvexity
open scoped BigOperators ENNReal Topology ContDiff Convolution
  ComplexConjugate ComplexOrder

private theorem momentWeakJointCoverUpperEnvelope_timeEmbedding_of_pos
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) {t : ℝ} (ht : 0 < t) :
    momentWeakJointCoverUpperEnvelope K F htransport p
      (sourceJointTimeEmbedding z t) =
        momentEnvelopeTimeSlice K F htransport p z t := by
  have htime :
      0 < sourceJointCoverTime (sourceJointTimeEmbedding z t) := by
    simpa only [sourceJointCoverTime_timeEmbedding] using ht
  calc
    momentWeakJointCoverUpperEnvelope K F htransport p
        (sourceJointTimeEmbedding z t) =
      momentWeakJointCoverEnvelope K F htransport p
        (sourceJointTimeEmbedding z t) :=
      (momentWeakJointCoverEnvelope_eq_upperEnvelope_of_pos
        K F htransport p (sourceJointTimeEmbedding z t) htime).symm
    _ = momentEnvelopeTimeSlice K F htransport p z t := by
      unfold momentWeakJointCoverEnvelope
      rw [sourceJointCoverTime_timeEmbedding]
      rfl

private theorem momentTorusEnvelopeTimeSlice_le_holomorphicJointMollification
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) {t : ℝ} (ht : 0 < t)
    (q : LogTorus n) :
    momentTorusEnvelopeTimeSlice K F htransport p q t ≤
      momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k
          (sourceJointTimeEmbedding (sourceTorusCoverPoint q) t) := by
  rw [momentTorusEnvelopeTimeSlice,
    ← momentWeakJointCoverUpperEnvelope_timeEmbedding_of_pos
      K F htransport p (sourceTorusCoverPoint q) ht]
  exact momentWeakJointCoverUpperEnvelope_le_trueRadialMollification
    K F htransport p k
      (sourceJointTimeEmbedding (sourceTorusCoverPoint q) t)

private theorem tendsto_momentWeakHolomorphicStrictJointCoverWeight
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 (0 : ℝ)))
    (q : SourceJointComplexCover n) :
    Tendsto
      (fun k : ℕ =>
        momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p (ε k) k q)
      atTop
      (𝓝 (momentWeakJointCoverUpperEnvelope
        K F htransport p q)) := by
  have hmoll :=
    tendsto_momentWeakHolomorphicJointTrueRadialMollification
      K F htransport p q
  have hone :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) :=
    tendsto_const_nhds
  have hreference :
      Tendsto
        (fun _ : ℕ =>
          matrixSourceCoverPotential
            (momentBodyStrictRadialPotential K) q.1)
        atTop
        (𝓝 (matrixSourceCoverPotential
          (momentBodyStrictRadialPotential K) q.1)) :=
    tendsto_const_nhds
  have hmix :=
    ((hone.sub hε).mul hmoll).add
      (hε.mul hreference)
  simpa only [momentWeakHolomorphicStrictJointCoverWeight, sub_zero, one_mul, zero_mul, add_zero]
    using hmix

private theorem tendsto_momentWeakHolomorphicStrictJointTorusWeight
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 (0 : ℝ)))
    {t : ℝ} (ht : 0 < t) (q : LogTorus n) :
    Tendsto
      (fun k : ℕ =>
        momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p (ε k) k t q)
      atTop
      (𝓝 (momentTorusEnvelopeTimeSlice
        K F htransport p q t)) := by
  have hcover :=
    tendsto_momentWeakHolomorphicStrictJointCoverWeight
      K F htransport p ε hε
        (sourceJointTimeEmbedding (sourceTorusCoverPoint q) t)
  rw [momentWeakJointCoverUpperEnvelope_timeEmbedding_of_pos
    K F htransport p (sourceTorusCoverPoint q) ht] at hcover
  simpa only [momentWeakHolomorphicStrictJointTorusWeight, jointSourceTorusWeight_eq_cover,
    momentTorusEnvelopeTimeSlice] using hcover

private def momentWeakHolomorphicUniformRadialRate
    {n : ℕ} (K : CenteredBody n) : ℝ :=
  min (((momentCoerciveMonomialDegree K : ℕ) : ℝ)⁻¹)
    (momentBodyStrictScale K)

private theorem momentWeakHolomorphicUniformRadialRate_pos
    {n : ℕ} (K : CenteredBody n) :
    0 < momentWeakHolomorphicUniformRadialRate K := by
  unfold momentWeakHolomorphicUniformRadialRate
  apply lt_min
  · apply inv_pos.mpr
    exact_mod_cast momentCoerciveMonomialDegree_pos K
  · exact momentBodyStrictScale_pos K

private def momentWeakHolomorphicUniformCoercivityConstant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) : ℝ :=
  max (momentTorusEnvelopeCoercivityConstant K F htransport) 0

private theorem momentWeakHolomorphicStrictJointTorusWeight_uniform_norm_coercivity
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) {t : ℝ} (ht : 0 < t)
    {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (q : LogTorus n) :
    momentWeakHolomorphicUniformRadialRate K * ‖q.1‖ -
        momentWeakHolomorphicUniformCoercivityConstant
          K F htransport ≤
      momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k t q := by
  let δ : ℝ :=
    (((momentCoerciveMonomialDegree K : ℕ) : ℝ)⁻¹)
  let s : ℝ := momentBodyStrictScale K
  let C : ℝ := momentTorusEnvelopeCoercivityConstant
    K F htransport
  let B : ℝ := max C 0
  let m : ℝ := min δ s
  have hnorm : 0 ≤ ‖q.1‖ := norm_nonneg _
  have hweak0 := momentTorusEnvelope_norm_coercivity
    K F htransport p q ht
  have hweak1 :=
    momentTorusEnvelopeTimeSlice_le_holomorphicJointMollification
      K F htransport p k ht q
  have hweak :
      δ * ‖q.1‖ - C ≤
        momentWeakHolomorphicJointTrueRadialMollification
          K F htransport p k
            (sourceJointTimeEmbedding (sourceTorusCoverPoint q) t) := by
    exact hweak0.trans hweak1
  have hrad :=
    momentWeakHolomorphicStrictRadialPotential_norm_lower K q.1
  have hmδ : m * ‖q.1‖ ≤ δ * ‖q.1‖ :=
    mul_le_mul_of_nonneg_right (min_le_left δ s) hnorm
  have hms : m * ‖q.1‖ ≤ s * ‖q.1‖ :=
    mul_le_mul_of_nonneg_right (min_le_right δ s) hnorm
  have hC : C ≤ B := le_max_left C 0
  have hB : 0 ≤ B := le_max_right C 0
  have hweight : 0 ≤ 1 - ε := sub_nonneg.mpr hε₁
  have hweak' := mul_le_mul_of_nonneg_left hweak hweight
  have hrad' := mul_le_mul_of_nonneg_left hrad hε₀
  have hmδ' := mul_le_mul_of_nonneg_left hmδ hweight
  have hms' := mul_le_mul_of_nonneg_left hms hε₀
  have hC' := mul_le_mul_of_nonneg_left hC hweight
  have hεB := mul_nonneg hε₀ hB
  rw [momentWeakHolomorphicStrictJointTorusWeight,
    jointSourceTorusWeight_eq_cover]
  unfold momentWeakHolomorphicStrictJointCoverWeight
  have href :
      matrixSourceCoverPotential
        (momentBodyStrictRadialPotential K)
        (sourceJointTimeEmbedding (sourceTorusCoverPoint q) t).1 =
        momentBodyStrictRadialPotential K q.1 := by
    simp only [sourceJointTimeEmbedding, sourceTorusCoverPoint,
      matrixSourceCoverPotential_logarithmicPoint]
  rw [href]
  change m * ‖q.1‖ - B ≤ _
  dsimp [δ, s, C, B, m] at *
  nlinarith

private def momentWeakHolomorphicUniformDensityMajorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (q : LogTorus n) : ℝ :=
  Real.exp
      (momentWeakHolomorphicUniformCoercivityConstant
        K F htransport) *
    (Real.exp
      (-momentWeakHolomorphicUniformRadialRate K * ‖q.1‖) *
      (1 : ℝ))

private theorem integrable_momentWeakHolomorphicUniformDensityMajorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    Integrable
      (momentWeakHolomorphicUniformDensityMajorant
        K F htransport)
      (sourceTorusBaseMeasure n) := by
  have hrad : Integrable
      (fun x : Space n =>
        Real.exp
          (-momentWeakHolomorphicUniformRadialRate K * ‖x‖))
      (volume : Measure (Space n)) :=
    integrable_exp_neg_mul_norm_all
      (momentWeakHolomorphicUniformRadialRate_pos K)
  have hang : Integrable
      (fun _ : AngularTorus n => (1 : ℝ))
      (angularMeasure n) :=
    integrable_const 1
  have hprod : Integrable
      (fun q : LogTorus n =>
        Real.exp
          (-momentWeakHolomorphicUniformRadialRate K * ‖q.1‖) *
            (1 : ℝ))
      (sourceTorusBaseMeasure n) := by
    simpa only [neg_mul, mul_one, sourceTorusBaseMeasure] using hrad.mul_prod hang
  change Integrable
    (fun q : LogTorus n =>
      Real.exp
          (momentWeakHolomorphicUniformCoercivityConstant
            K F htransport) *
        (Real.exp
          (-momentWeakHolomorphicUniformRadialRate K * ‖q.1‖) *
            (1 : ℝ)))
    (sourceTorusBaseMeasure n)
  exact hprod.const_mul
    (Real.exp
      (momentWeakHolomorphicUniformCoercivityConstant
        K F htransport))

private theorem exp_neg_momentWeakHolomorphicStrictJointTorusWeight_le_uniform
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) {t : ℝ} (ht : 0 < t)
    {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (q : LogTorus n) :
    Real.exp
        (-momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k t q) ≤
      momentWeakHolomorphicUniformDensityMajorant
        K F htransport q := by
  unfold momentWeakHolomorphicUniformDensityMajorant
  simp only [mul_one]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hcoerce :=
    momentWeakHolomorphicStrictJointTorusWeight_uniform_norm_coercivity
      K F htransport p k ht hε₀ hε₁ q
  linarith

private theorem tendsto_momentWeakHolomorphicStrictJointTimeDensity
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 (0 : ℝ)))
    {t : ℝ} (ht : 0 < t) (q : LogTorus n) :
    Tendsto
      (fun k : ℕ =>
        sourceTimeDensity
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p (ε k) k) t q)
      atTop
      (𝓝 (sourceTimeDensity
        (fun (u : ℝ) (w : LogTorus n) =>
          momentTorusEnvelopeTimeSlice K F htransport p w u)
        t q)) := by
  have hweight :=
    tendsto_momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p ε hε ht q
  change Tendsto
    (fun k : ℕ =>
      Real.exp
        (-momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p (ε k) k t q))
    atTop
    (𝓝 (Real.exp
      (-momentTorusEnvelopeTimeSlice
        K F htransport p q t)))
  have h := Real.continuous_exp.continuousAt.tendsto.comp hweight.neg
  refine h.congr' (Filter.Eventually.of_forall fun k => ?_)
  rfl

private theorem tendsto_momentWeakHolomorphicStrictJointPartition
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 (0 : ℝ)))
    (hε₀ : ∀ k : ℕ, 0 ≤ ε k)
    (hε₁ : ∀ k : ℕ, ε k ≤ 1)
    {t : ℝ} (ht : 0 < t) :
    Tendsto
      (fun k : ℕ =>
        sourcePartition
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p (ε k) k) t)
      atTop
      (𝓝 (sourcePartition
        (fun (u : ℝ) (q : LogTorus n) =>
          momentTorusEnvelopeTimeSlice K F htransport p q u)
        t)) := by
  have hmajor :=
    integrable_momentWeakHolomorphicUniformDensityMajorant
      K F htransport
  have hdom :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := sourceTorusBaseMeasure n)
      (l := Filter.atTop)
      (F := fun (k : ℕ) (q : LogTorus n) =>
        sourceTimeDensity
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p (ε k) k) t q)
      (f := fun q : LogTorus n =>
        sourceTimeDensity
          (fun (u : ℝ) (w : LogTorus n) =>
            momentTorusEnvelopeTimeSlice K F htransport p w u)
          t q)
      (momentWeakHolomorphicUniformDensityMajorant
        K F htransport)
      (Filter.Eventually.of_forall fun k =>
        (Real.continuous_exp.comp
          (continuous_momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p (ε k) k t).neg).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun k =>
        Filter.Eventually.of_forall fun q => by
          change
            |Real.exp
              (-momentWeakHolomorphicStrictJointTorusWeight
                K F htransport p (ε k) k t q)| ≤
              momentWeakHolomorphicUniformDensityMajorant
                K F htransport q
          rw [abs_of_pos (Real.exp_pos _)]
          exact
            exp_neg_momentWeakHolomorphicStrictJointTorusWeight_le_uniform
              K F htransport p k ht (hε₀ k) (hε₁ k) q)
      hmajor
      (Filter.Eventually.of_forall fun q =>
        tendsto_momentWeakHolomorphicStrictJointTimeDensity
          K F htransport p ε hε ht q)
  simpa only [sourcePartition] using hdom

private theorem tendsto_momentWeakHolomorphicStrictJointLogPartition
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 (0 : ℝ)))
    (hε₀ : ∀ k : ℕ, 0 ≤ ε k)
    (hε₁ : ∀ k : ℕ, ε k ≤ 1)
    {t : ℝ} (ht : 0 < t) :
    Tendsto
      (fun k : ℕ =>
        sourceLogPartition
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p (ε k) k) t)
      atTop
      (𝓝 (sourceLogPartition
        (fun (u : ℝ) (q : LogTorus n) =>
          momentTorusEnvelopeTimeSlice K F htransport p q u)
        t)) := by
  have hpart :=
    tendsto_momentWeakHolomorphicStrictJointPartition
      K F htransport p ε hε hε₀ hε₁ ht
  have hpos := momentTorusEnvelopePartition_pos
    K F htransport p t
  have hlog :=
    (Real.continuousAt_log hpos.ne').tendsto.comp hpart
  simpa only [sourceLogPartition, sourcePartition, sourceTimeDensity, tendsto_neg_iff, comp_apply]
    using hlog.neg

end BergmanJetJointHolomorphicPhysicalApproximation

namespace BergmanJetTorusRightSlopeBridge

open Set Function Filter MeasureTheory Metric
open TorusCharacters WeightedTorusHilbert SupportFunction LaplaceAsymptotics BergmanMonomials
open BergmanGeodesicConvexity JetEnvelopeRightDerivative ActualJetUpperEnvelope MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation MomentRegularity MomentWeakGlobalKernel
open BergmanJetGeodesic BergmanJetProfileBridge BergmanJetRealGeodesic BergmanJetUpperEnvelope
open BergmanJetEnvelopeLimit BergmanJetTorusEnvelope BergmanJetTorusSlopeBridge
open BergmanJetPointwiseLogKernel
open scoped BigOperators ENNReal InnerProductSpace Topology

private theorem momentTorusTruncatedJetOrderDensity_nonneg
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (N : ℕ) (q : LogTorus n) :
    0 ≤ momentTorusTruncatedJetOrderDensity
      K hk F htransport p N q := by
  unfold momentTorusTruncatedJetOrderDensity
    momentTorusJetBasisWeight
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)

private theorem momentTorusTruncatedJetOrderDensity_le_diagonal_mul_cutoff
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (N : ℕ) (q : LogTorus n) :
    momentTorusTruncatedJetOrderDensity
      K hk F htransport p N q ≤
        (N : ℝ) * diagonalKernel K k
          (momentNormalizedPotential F) q.1 := by
  have hdiag :
      (∑ i : Fin (bergmanDimension K k),
        momentTorusJetBasisWeight
          K hk F htransport p q i) =
        diagonalKernel K k
          (momentNormalizedPotential F) q.1 := by
    simpa only [momentTorusJetBasisWeight] using
      (sum_momentTorusRepresentative_normSq_eq_diagonalKernel
        K hk F htransport
          (momentSimultaneousJetBasis K hk F htransport p) q)
  calc
    momentTorusTruncatedJetOrderDensity
        K hk F htransport p N q ≤
      ∑ i : Fin (bergmanDimension K k),
        (N : ℝ) * momentTorusJetBasisWeight
          K hk F htransport p q i := by
      unfold momentTorusTruncatedJetOrderDensity
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast
          momentTruncatedJetOrder_le
            K hk F htransport p N i
      · exact Complex.normSq_nonneg _
    _ = (N : ℝ) *
        (∑ i : Fin (bergmanDimension K k),
          momentTorusJetBasisWeight
            K hk F htransport p q i) := by
      rw [Finset.mul_sum]
    _ = (N : ℝ) * diagonalKernel K k
          (momentNormalizedPotential F) q.1 := by
      rw [hdiag]

private theorem momentPositiveTorusJetSlope_nonneg
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (N : ℕ) (q : LogTorus n) :
    0 ≤ momentPositiveTorusJetSlope
      K hk F htransport p N q := by
  unfold momentPositiveTorusJetSlope
  exact div_nonneg
    (momentTorusTruncatedJetOrderDensity_nonneg
      K hk F htransport p N q)
    (mul_nonneg (by exact_mod_cast hk.le)
      (diagonalKernel_momentNormalized_pos
        K hk F htransport q.1).le)

private theorem momentPositiveTorusJetSlope_le_cutoff
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (N : ℕ) (q : LogTorus n) :
    momentPositiveTorusJetSlope
        K hk F htransport p N q ≤
      (N : ℝ) / (k : ℝ) := by
  have hkreal : 0 < (k : ℝ) := by
    exact_mod_cast hk
  have hdiag :=
    diagonalKernel_momentNormalized_pos
      K hk F htransport q.1
  unfold momentPositiveTorusJetSlope
  apply (div_le_iff₀ (mul_pos hkreal hdiag)).mpr
  calc
    momentTorusTruncatedJetOrderDensity
        K hk F htransport p N q ≤
      (N : ℝ) * diagonalKernel K k
        (momentNormalizedPotential F) q.1 :=
      momentTorusTruncatedJetOrderDensity_le_diagonal_mul_cutoff
        K hk F htransport p N q
    _ = ((N : ℝ) / (k : ℝ)) *
        ((k : ℝ) * diagonalKernel K k
          (momentNormalizedPotential F) q.1) := by
      field_simp

private theorem momentPositiveTorusJetSlope_le_canonicalScale
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (q : LogTorus n) :
    momentPositiveTorusJetSlope
        K hk F htransport p
          (Nat.floor
            (BodyScale.canonicalScale K * (k : ℝ))) q ≤
      BodyScale.canonicalScale K := by
  have hkreal : 0 < (k : ℝ) := by
    exact_mod_cast hk
  calc
    momentPositiveTorusJetSlope
        K hk F htransport p
          (Nat.floor
            (BodyScale.canonicalScale K * (k : ℝ))) q ≤
      ((Nat.floor
          (BodyScale.canonicalScale K * (k : ℝ)) : ℕ) : ℝ) /
        (k : ℝ) :=
      momentPositiveTorusJetSlope_le_cutoff
        K hk F htransport p _ q
    _ ≤ BodyScale.canonicalScale K :=
      (div_le_iff₀ hkreal).mpr
        (Nat.floor_le
          (mul_nonneg
            (BodyScale.canonicalScale_pos K).le hkreal.le))

private theorem continuous_momentPositiveTorusJetSlope
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (N : ℕ) :
    Continuous
      (momentPositiveTorusJetSlope
        K hk F htransport p N) := by
  have hkreal : 0 < (k : ℝ) := by
    exact_mod_cast hk
  unfold momentPositiveTorusJetSlope
  apply
    (continuous_momentTorusTruncatedJetOrderDensity
      K hk F htransport p N).div
      (continuous_const.mul
        ((continuous_momentDiagonalKernel K hk F).comp
          continuous_fst))
  intro q
  exact
    (mul_pos hkreal
      (diagonalKernel_momentNormalized_pos
        K hk F htransport q.1)).ne'

private def momentTorusJetSlope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (q : LogTorus n) : ℝ :=
  if hk : 0 < k then
    momentPositiveTorusJetSlope
      K hk F htransport p
        (Nat.floor
          (BodyScale.canonicalScale K * (k : ℝ))) q
  else 0

private theorem momentTorusJetSlope_nonneg
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (q : LogTorus n) :
    0 ≤ momentTorusJetSlope K F htransport p k q := by
  unfold momentTorusJetSlope
  split
  · exact momentPositiveTorusJetSlope_nonneg
      K ‹0 < k› F htransport p _ q
  · exact le_rfl

private theorem momentTorusJetSlope_le_canonicalScale
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (q : LogTorus n) :
    momentTorusJetSlope K F htransport p k q ≤
      BodyScale.canonicalScale K := by
  unfold momentTorusJetSlope
  split
  · exact momentPositiveTorusJetSlope_le_canonicalScale
      K ‹0 < k› F htransport p q
  · exact (BodyScale.canonicalScale_pos K).le

private theorem continuous_momentTorusJetSlope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) :
    Continuous (momentTorusJetSlope K F htransport p k) := by
  classical
  change
    Continuous (fun q : LogTorus n =>
      if hk : 0 < k then
        momentPositiveTorusJetSlope
          K hk F htransport p
            (Nat.floor
              (BodyScale.canonicalScale K * (k : ℝ))) q
      else 0)
  by_cases hk : 0 < k
  · simpa only [hk, ↓reduceDIte] using
      (continuous_momentPositiveTorusJetSlope
        K hk F htransport p
        (Nat.floor
          (BodyScale.canonicalScale K * (k : ℝ))))
  · simpa only [hk, ↓reduceDIte] using
      (continuous_const :
        Continuous (fun _ : LogTorus n => (0 : ℝ)))

private theorem momentCoverMoment_zero_eq_torusTruncatedJetOrderDensity
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (N : ℕ) (q : LogTorus n) :
    exponentialMoment
        (momentHolomorphicBasisWeight
          K hk F htransport
          (momentSimultaneousJetBasis K hk F htransport p)
          (sourceTorusCoverPoint q))
        (momentTruncatedJetOrder K hk F htransport p N)
        1 0 =
      momentTorusTruncatedJetOrderDensity
        K hk F htransport p N q := by
  unfold exponentialMoment momentTorusTruncatedJetOrderDensity
  simp only [pow_one, zero_mul, Real.exp_zero, mul_one]
  apply Finset.sum_congr rfl
  intro i _
  unfold momentHolomorphicBasisWeight
    momentTorusJetBasisWeight
  rw [momentTorusRepresentative_eq_holomorphicRepresentative_cover]
  ring

private theorem momentCoverPartition_zero_eq_diagonalKernel
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (N : ℕ) (q : LogTorus n) :
    exponentialPartition
        (momentHolomorphicBasisWeight
          K hk F htransport
          (momentSimultaneousJetBasis K hk F htransport p)
          (sourceTorusCoverPoint q))
        (momentTruncatedJetOrder K hk F htransport p N) 0 =
      diagonalKernel K k
        (momentNormalizedPotential F) q.1 := by
  unfold exponentialPartition exponentialMoment
  simp only [pow_zero, zero_mul, Real.exp_zero, mul_one]
  simpa only [realLogCoordinate_sourceTorusCoverPoint] using
    (sum_momentHolomorphicBasisWeight_eq_diagonalKernel
      K hk F htransport
        (momentSimultaneousJetBasis K hk F htransport p)
        (sourceTorusCoverPoint q))

private theorem momentPositiveTorusJetSlope_eq_deriv_cover
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (N : ℕ) (q : LogTorus n) :
    momentPositiveTorusJetSlope
      K hk F htransport p N q =
        deriv
          (momentJetGeodesic K hk F htransport p N
            (sourceTorusCoverPoint q)) 0 := by
  unfold momentJetGeodesic
  rw [(hasDerivAt_logarithmicPotential
    (momentHolomorphicBasisWeight
      K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p)
      (sourceTorusCoverPoint q))
    (momentTruncatedJetOrder K hk F htransport p N)
    (momentHolomorphicBasisWeight_nonneg
      K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p)
      (sourceTorusCoverPoint q))
    (exists_positive_momentHolomorphicBasisWeight
      K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p)
      (sourceTorusCoverPoint q))
    (k : ℝ) 0).deriv]
  rw [momentCoverMoment_zero_eq_torusTruncatedJetOrderDensity
    K hk F htransport p N q,
    momentCoverPartition_zero_eq_diagonalKernel
      K hk F htransport p N q]
  unfold momentPositiveTorusJetSlope
  ring

private theorem momentPositiveTorusJetSlope_le_cover_positive_secant
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (N : ℕ) (q : LogTorus n)
    {t : ℝ} (ht : 0 < t) :
    momentPositiveTorusJetSlope
        K hk F htransport p N q ≤
      (momentJetGeodesic K hk F htransport p N
          (sourceTorusCoverPoint q) t -
        momentJetGeodesic K hk F htransport p N
          (sourceTorusCoverPoint q) 0) / t := by
  rw [momentPositiveTorusJetSlope_eq_deriv_cover]
  have hdiff :
      DifferentiableAt ℝ
        (momentJetGeodesic K hk F htransport p N
          (sourceTorusCoverPoint q)) 0 := by
    unfold momentJetGeodesic
    exact (hasDerivAt_logarithmicPotential
      (momentHolomorphicBasisWeight
        K hk F htransport
        (momentSimultaneousJetBasis K hk F htransport p)
        (sourceTorusCoverPoint q))
      (momentTruncatedJetOrder K hk F htransport p N)
      (momentHolomorphicBasisWeight_nonneg
        K hk F htransport
        (momentSimultaneousJetBasis K hk F htransport p)
        (sourceTorusCoverPoint q))
      (exists_positive_momentHolomorphicBasisWeight
        K hk F htransport
        (momentSimultaneousJetBasis K hk F htransport p)
        (sourceTorusCoverPoint q))
      (k : ℝ) 0).differentiableAt
  have h :=
    (convexOn_momentJetGeodesic
      K hk F htransport p N (sourceTorusCoverPoint q)).deriv_le_slope
        (Set.mem_univ (0 : ℝ)) (Set.mem_univ t) ht hdiff
  simpa only [ge_iff_le, slope_def_field, sub_zero] using h

private theorem momentPositiveJointGeodesic_le_tailUpperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r k : ℕ)
    (hk : momentJointTailStart K F htransport p + r ≤ k)
    (w : PositiveJointLogSpace n) :
    momentPositiveJointGeodesic K F htransport p k w ≤
      momentJointTailUpperEnvelope K F htransport p r w := by
  calc
    momentPositiveJointGeodesic K F htransport p k w ≤
      momentJointTailSup K F htransport p r w := by
      unfold momentJointTailSup
      apply le_csSup
        (momentJointTailSup_range_bddAbove
          K F htransport p r w)
      refine ⟨k - (momentJointTailStart
        K F htransport p + r), ?_⟩
      change
        momentPositiveJointGeodesic K F htransport p
          (momentJointTailStart K F htransport p + r +
            (k - (momentJointTailStart
              K F htransport p + r))) w =
          momentPositiveJointGeodesic K F htransport p k w
      rw [Nat.add_sub_of_le hk]
    _ ≤ momentJointTailUpperEnvelope K F htransport p r w :=
      ActualJetUpperEnvelope.le_upperRegularization
        (momentJointTailSup K F htransport p r) w
        (momentJointTailSup_localUpperBounds_nonempty
          K F htransport p r w)

private theorem limsup_momentTorusJetSlope_le_tail_positive_secant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (q : LogTorus n)
    {u : Space n} (hu : u ∈ interior K.carrier)
    (hmax : ∀ x : Space n,
      phase u (momentNormalizedPotential F) x ≤
        phase u (momentNormalizedPotential F) q.1)
    (r : ℕ) {t : ℝ} (ht : 0 < t) :
    Filter.limsup
        (fun k : ℕ =>
          momentTorusJetSlope K F htransport p k q) atTop ≤
      (momentJointTailUpperEnvelope K F htransport p r
          (sourcePositiveJointTimePoint
            (sourceTorusCoverPoint q) t ht) -
        momentNormalizedPotential F q.1) / t := by
  let z := sourceTorusCoverPoint q
  let B := momentJointTailUpperEnvelope K F htransport p r
    (sourcePositiveJointTimePoint z t ht)
  have hcob := Filter.isCoboundedUnder_le_of_le atTop
    (fun k => momentTorusJetSlope_nonneg
      K F htransport p k q)
  have hbounded :
      Filter.IsBoundedUnder (· ≤ ·) atTop
        (fun k : ℕ =>
          momentTorusJetSlope K F htransport p k q) :=
    Filter.isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall fun k =>
        momentTorusJetSlope_le_canonicalScale
          K F htransport p k q)
  change
    Filter.limsup
        (fun k : ℕ =>
          momentTorusJetSlope K F htransport p k q) atTop ≤
      (B - momentNormalizedPotential F q.1) / t
  apply (Filter.limsup_le_iff hcob hbounded).mpr
  intro a ha
  have hthreshold :
      B - a * t < momentNormalizedPotential F q.1 := by
    have hcross := (div_lt_iff₀ ht).mp ha
    linarith
  have hzero :=
    (tendsto_order.mp
      (tendsto_log_momentNormalized_diagonalKernel_div
        K F htransport hu q.1 hmax)).1
      (B - a * t) hthreshold
  filter_upwards
    [eventually_ge_atTop
      (momentJointTailStart K F htransport p + r + 1),
      hzero] with k hk hlog
  have hkpos : 0 < k := by omega
  have htail :
      momentJointTailStart K F htransport p + r ≤ k - 1 := by
    omega
  have hkadd : k - 1 + 1 = k := by omega
  let N := Nat.floor
    (BodyScale.canonicalScale K * (k : ℝ))
  have htime :
      momentJetGeodesic K hkpos F htransport p N z t ≤ B := by
    have hfinite :=
      momentPositiveJointGeodesic_le_tailUpperEnvelope
        K F htransport p r (k - 1) htail
          (sourcePositiveJointTimePoint z t ht)
    rw [momentPositiveJointGeodesic_eq_momentJetGeodesic,
      jointLogTime_sourcePositiveJointTimePoint] at hfinite
    simpa [hkadd, N, B, sourcePositiveJointTimePoint]
      using hfinite
  have hzeroeq :
      momentJetGeodesic K hkpos F htransport p N z 0 =
        Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) q.1) / (k : ℝ) := by
    rw [momentJetGeodesic_zero_eq_log_diagonalKernel,
      realLogCoordinate_sourceTorusCoverPoint]
  have hfiniteSlope :=
    momentPositiveTorusJetSlope_le_cover_positive_secant
      K hkpos F htransport p N q ht
  have hslope :
      momentTorusJetSlope K F htransport p k q ≤
        (B - Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) q.1) /
              (k : ℝ)) / t := by
    simp only [momentTorusJetSlope, dite_eq_left hkpos]
    change momentPositiveTorusJetSlope
      K hkpos F htransport p N q ≤ _
    calc
      momentPositiveTorusJetSlope
          K hkpos F htransport p N q ≤
        (momentJetGeodesic K hkpos F htransport p N z t -
          momentJetGeodesic K hkpos F htransport p N z 0) / t :=
        hfiniteSlope
      _ ≤
        (B - Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) q.1) /
              (k : ℝ)) / t := by
        rw [hzeroeq]
        exact (div_le_div_iff_of_pos_right ht).mpr
          (sub_le_sub_right htime _)
  apply lt_of_le_of_lt hslope
  apply (div_lt_iff₀ ht).mpr
  linarith

private theorem limsup_momentTorusJetSlope_le_envelope_positive_secant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (q : LogTorus n)
    {u : Space n} (hu : u ∈ interior K.carrier)
    (hmax : ∀ x : Space n,
      phase u (momentNormalizedPotential F) x ≤
        phase u (momentNormalizedPotential F) q.1)
    {t : ℝ} (ht : 0 < t) :
    Filter.limsup
        (fun k : ℕ =>
          momentTorusJetSlope K F htransport p k q) atTop ≤
      (momentTorusEnvelopeTimeSlice
          K F htransport p q t -
        momentTorusEnvelopeTimeSlice
          K F htransport p q 0) / t := by
  let z := sourceTorusCoverPoint q
  let w := sourcePositiveJointTimePoint z t ht
  have htail :=
    tendsto_momentJointTailUpperEnvelope
      K F htransport p w
  have hquot :
      Tendsto
        (fun r : ℕ =>
          (momentJointTailUpperEnvelope
            K F htransport p r w -
              momentNormalizedPotential F q.1) / t)
        atTop
        (𝓝 ((momentJointUpperEnvelope
          K F htransport p w -
            momentNormalizedPotential F q.1) / t)) :=
    (htail.sub_const
      (momentNormalizedPotential F q.1)).div_const t
  have hle :
      Filter.limsup
          (fun k : ℕ =>
            momentTorusJetSlope K F htransport p k q) atTop ≤
        (momentJointUpperEnvelope
          K F htransport p w -
            momentNormalizedPotential F q.1) / t := by
    apply ge_of_tendsto hquot
    exact Filter.Eventually.of_forall fun r =>
      limsup_momentTorusJetSlope_le_tail_positive_secant
        K F htransport p q hu hmax r ht
  simpa only [momentTorusEnvelopeTimeSlice, momentEnvelopeTimeSlice, ht, ↓reduceDIte,
    lt_self_iff_false, realLogCoordinate_sourceTorusCoverPoint, ge_iff_le] using hle

private theorem ae_limsup_momentTorusJetSlope_le_envelope_positive_secant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ x : Space n
      ∂(volume : Measure (Space n)),
      ∀ θ : AngularTorus n,
        Filter.limsup
            (fun k : ℕ =>
              momentTorusJetSlope
                K F htransport p k (x, θ)) atTop ≤
          (momentTorusEnvelopeTimeSlice
              K F htransport p (x, θ) t -
            momentTorusEnvelopeTimeSlice
              K F htransport p (x, θ) 0) / t := by
  filter_upwards
    [ae_differentiableAt_finiteEnergySource F,
      ae_finiteEnergySourceGradient_mem_interior_volume
        F htransport] with x hx hinterior θ
  let u : Space n :=
    SpatialBergmanFatouScheffe.actualGradient F.potential x
  have hmax : ∀ z : Space n,
      phase u (momentNormalizedPotential F) z ≤
        phase u (momentNormalizedPotential F) x := by
    intro z
    have h := finiteEnergySourcePhase_actualGradient_le F x hx z
    change phase u F.potential z ≤ phase u F.potential x at h
    unfold phase at h ⊢
    change
      pairing u z -
          (F.potential z +
            Real.log
              (finiteEnergySourcePartition F /
                normalizedVolume K.carrier)) ≤
        pairing u x -
          (F.potential x +
            Real.log
              (finiteEnergySourcePartition F /
                normalizedVolume K.carrier))
    linarith
  exact limsup_momentTorusJetSlope_le_envelope_positive_secant
    K F htransport p (x, θ) hinterior hmax ht

end BergmanJetTorusRightSlopeBridge

namespace BergmanJetTorusRightSlopeGibbsBridge

open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence LogPartitionConvexity
open MomentOptimizer MomentTargetGeodesic MomentFirstVariation MomentRegularity
open BergmanJetTorusEnvelope BergmanJetPartitionEndpoint BergmanJetTorusSlopeBridge
open BergmanJetTorusRightSlopeBridge
open scoped BigOperators ENNReal Topology

private theorem eventually_integral_momentTorusJetSlope_Bergman_ge_sharp
    {n : ℕ} (hn : 0 < n) (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      (n : ℝ) * BodyScale.canonicalScale K /
          ((n : ℝ) + 1) - ε ≤
        ∫ q : LogTorus n,
          momentTorusJetSlope K F htransport p k q
            ∂(momentTorusBergmanProbability K F k) := by
  filter_upwards
    [eventually_integral_momentPositiveTorusJetSlope_ge_sharp
      hn K F htransport p hε,
      eventually_gt_atTop (0 : ℕ)] with k hprofile hk
  simpa only [momentTorusJetSlope, dite_eq_left hk]
    using hprofile hk

private def momentBodyEnvelopePositiveSecant
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) (q : LogTorus n) : ℝ :=
  (momentBodyTorusWeight K p t q -
    momentBodyTorusWeight K p 0 q) / t

private theorem momentBodyEnvelopePositiveSecant_le_canonicalScale
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) {t : ℝ} (ht : 0 < t)
    (q : LogTorus n) :
    momentBodyEnvelopePositiveSecant K p t q ≤
      BodyScale.canonicalScale K := by
  unfold momentBodyEnvelopePositiveSecant
  apply (div_le_iff₀ ht).mpr
  rw [momentBodyTorusWeight_zero]
  have h := momentTorusEnvelopeTimeSlice_le_normalized_add
    K (momentBodyOptimizer K)
      (momentBodyOptimizer_transport K) p q ht
  change
    momentBodyTorusWeight K p t q ≤
      momentNormalizedPotential (momentBodyOptimizer K) q.1 +
        BodyScale.canonicalScale K * t at h
  linarith

private theorem measurable_momentBodyEnvelopePositiveSecant
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) :
    Measurable (momentBodyEnvelopePositiveSecant K p t) := by
  unfold momentBodyEnvelopePositiveSecant
  exact ((measurable_momentBodyTorusWeight K p t).sub
    (measurable_momentBodyTorusWeight K p 0)).div_const t

private theorem ae_limsup_momentTorusJetSlope_le_bodySecant_base
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ q : LogTorus n ∂(sourceTorusBaseMeasure n),
      Filter.limsup
          (fun k : ℕ => momentTorusJetSlope
            K (momentBodyOptimizer K)
              (momentBodyOptimizer_transport K) p k q) atTop ≤
        momentBodyEnvelopePositiveSecant K p t q := by
  have hrad :=
    ae_limsup_momentTorusJetSlope_le_envelope_positive_secant
      K (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K) p ht
  have hprod :=
    (Measure.quasiMeasurePreserving_fst
      (μ := (volume : Measure (Space n)))
      (ν := angularMeasure n)).ae hrad
  change
    ∀ᵐ q : LogTorus n
      ∂((volume : Measure (Space n)).prod
        (angularMeasure n)),
      Filter.limsup
          (fun k : ℕ => momentTorusJetSlope
            K (momentBodyOptimizer K)
              (momentBodyOptimizer_transport K) p k q) atTop ≤
        momentBodyEnvelopePositiveSecant K p t q
  filter_upwards [hprod] with q hq
  simpa only [momentBodyEnvelopePositiveSecant, momentBodyTorusWeight,
    momentTorusEnvelopeTimeSlice_zero, Prod.mk.eta] using hq q.2

private theorem ae_limsup_momentTorusJetSlope_le_bodySecant_Gibbs
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ q : LogTorus n
      ∂(sourceProbability (momentBodyTorusWeight K p) 0),
      Filter.limsup
          (fun k : ℕ => momentTorusJetSlope
            K (momentBodyOptimizer K)
              (momentBodyOptimizer_transport K) p k q) atTop ≤
        momentBodyEnvelopePositiveSecant K p t q := by
  have hbase :=
    ae_limsup_momentTorusJetSlope_le_bodySecant_base K p ht
  change
    ∀ᵐ q : LogTorus n
      ∂((sourceTorusBaseMeasure n).withDensity
        (fun q => ENNReal.ofReal
          (sourceNormalizedDensity
            (momentBodyTorusWeight K p) 0 q))),
      Filter.limsup
          (fun k : ℕ => momentTorusJetSlope
            K (momentBodyOptimizer K)
              (momentBodyOptimizer_transport K) p k q) atTop ≤
        momentBodyEnvelopePositiveSecant K p t q
  exact (withDensity_absolutelyContinuous
    (sourceTorusBaseMeasure n)
    (fun q => ENNReal.ofReal
      (sourceNormalizedDensity
        (momentBodyTorusWeight K p) 0 q))).ae_le hbase

private theorem ae_momentBodyEnvelopePositiveSecant_nonneg_Gibbs
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ q : LogTorus n
      ∂(sourceProbability (momentBodyTorusWeight K p) 0),
      0 ≤ momentBodyEnvelopePositiveSecant K p t q := by
  filter_upwards
    [ae_limsup_momentTorusJetSlope_le_bodySecant_Gibbs
      K p ht] with q hq
  have hbounded :
      Filter.IsBoundedUnder (· ≤ ·) atTop
        (fun k : ℕ => momentTorusJetSlope
          K (momentBodyOptimizer K)
            (momentBodyOptimizer_transport K) p k q) :=
    Filter.isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall fun k =>
        momentTorusJetSlope_le_canonicalScale
          K (momentBodyOptimizer K)
            (momentBodyOptimizer_transport K) p k q)
  have hnonneg :
      0 ≤ Filter.limsup
        (fun k : ℕ => momentTorusJetSlope
          K (momentBodyOptimizer K)
            (momentBodyOptimizer_transport K) p k q) atTop :=
    Filter.le_limsup_of_frequently_le
      (Filter.Eventually.of_forall fun k =>
        momentTorusJetSlope_nonneg
          K (momentBodyOptimizer K)
            (momentBodyOptimizer_transport K) p k q).frequently
      hbounded
  exact hnonneg.trans hq

private theorem integrable_momentBodyEnvelopePositiveSecant_Gibbs
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) {t : ℝ} (ht : 0 < t) :
    Integrable (momentBodyEnvelopePositiveSecant K p t)
      (sourceProbability (momentBodyTorusWeight K p) 0) := by
  let := sourceProbability_momentBody_isProbability K p 0
  refine (integrable_const (BodyScale.canonicalScale K)).mono'
    (measurable_momentBodyEnvelopePositiveSecant
      K p t).aestronglyMeasurable ?_
  filter_upwards
    [ae_momentBodyEnvelopePositiveSecant_nonneg_Gibbs
      K p ht] with q hq
  rw [Real.norm_eq_abs, abs_of_nonneg hq]
  exact momentBodyEnvelopePositiveSecant_le_canonicalScale
    K p ht q

end BergmanJetTorusRightSlopeGibbsBridge

namespace BergmanJetPortmanteauSlopeBridge

open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert WeightedTorusDistributionBridge MatrixTorusBochnerIdentity
open scoped BigOperators ENNReal NNReal Topology

private theorem limsup_measureReal_closed_le_of_probability_tendsto
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    (μ : ProbabilityMeasure X) (μk : ℕ → ProbabilityMeasure X)
    (hμ : Tendsto μk atTop (𝓝 μ))
    {S : Set X} (hS : IsClosed S) :
    Filter.limsup
        (fun k : ℕ => (μk k : Measure X).real S) atTop ≤
      (μ : Measure X).real S := by
  have hclosed :=
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ hS
  have hbound :
      ∀ᶠ k : ℕ in atTop, (μk k : Measure X) S ≤ (1 : ℝ≥0∞) :=
    Filter.Eventually.of_forall fun k =>
      @prob_le_one X _ (μk k : Measure X) inferInstance S
  change
    Filter.limsup
        (fun k : ℕ => ((μk k : Measure X) S).toReal) atTop ≤
      ((μ : Measure X) S).toReal
  rw [ENNReal.limsup_toReal_eq ENNReal.one_ne_top hbound]
  exact ENNReal.toReal_mono (measure_ne_top (μ : Measure X) S) hclosed

private theorem upperSemicontinuous_of_complexTorusCover
    {n : ℕ} (f : LogTorus n → ℝ)
    (hf : UpperSemicontinuous
      (fun z : LogSpace n =>
        f (complexTorusCoverProjection n z))) :
    UpperSemicontinuous f := by
  apply upperSemicontinuous_iff_isOpen_preimage.mpr
  intro a
  apply (complexTorusCoverProjection_isOpenQuotientMap n).isQuotientMap.isOpen_preimage.mp
  change IsOpen
    ((fun z : LogSpace n =>
      f (complexTorusCoverProjection n z)) ⁻¹' Set.Iio a)
  exact hf.isOpen_preimage a

end BergmanJetPortmanteauSlopeBridge

namespace BergmanJetPortmanteauUpperTailBridge

open Set Function Filter MeasureTheory
open scoped BigOperators ENNReal NNReal Topology

private theorem measurable_measureReal_upperLevel
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (g : X → ℝ) :
    Measurable (fun t : ℝ => μ.real {x : X | t ≤ g x}) := by
  apply Measurable.ennreal_toReal
  exact Antitone.measurable fun s t hst =>
    measure_mono fun x hx => le_trans hst hx

private theorem integrable_upperSemicontinuous_of_probability_bound
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X]
    (μ : ProbabilityMeasure X) {g : X → ℝ} {C : ℝ}
    (hg : UpperSemicontinuous g)
    (hC : 0 ≤ C) (hnonneg : ∀ x : X, 0 ≤ g x)
    (hbound : ∀ x : X, g x ≤ C) :
    Integrable g (μ : Measure X) := by
  refine (integrable_const C).mono' hg.measurable.aestronglyMeasurable ?_
  have hCabs : |C| = C := abs_of_nonneg hC
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg x)] using hbound x

end BergmanJetPortmanteauUpperTailBridge

namespace BergmanJetPortmanteauMovingUpperTailBridge

open Set Function Filter MeasureTheory
open BergmanJetPortmanteauSlopeBridge BergmanJetPortmanteauUpperTailBridge
open scoped BigOperators ENNReal NNReal Topology

private def movingUpperLevelClosedTail
    {X : Type*} [TopologicalSpace X]
    (f : ℕ → X → ℝ) (t : ℝ) (N : ℕ) : Set X :=
  closure (⋃ k : ℕ, ⋃ (_ : N ≤ k), {x : X | t ≤ f k x})

private theorem isClosed_movingUpperLevelClosedTail
    {X : Type*} [TopologicalSpace X]
    (f : ℕ → X → ℝ) (t : ℝ) (N : ℕ) :
    IsClosed (movingUpperLevelClosedTail f t N) :=
  isClosed_closure

private theorem antitone_movingUpperLevelClosedTail
    {X : Type*} [TopologicalSpace X]
    (f : ℕ → X → ℝ) (t : ℝ) :
    Antitone (movingUpperLevelClosedTail f t) := by
  intro m n hmn
  apply closure_mono
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
  rcases Set.mem_iUnion.mp hk with ⟨hnk, hxk⟩
  exact Set.mem_iUnion.mpr
    ⟨k, Set.mem_iUnion.mpr ⟨le_trans hmn hnk, hxk⟩⟩

private theorem moving_upperLevel_subset_closedTail
    {X : Type*} [TopologicalSpace X]
    (f : ℕ → X → ℝ) (t : ℝ)
    {N k : ℕ} (hk : N ≤ k) :
    {x : X | t ≤ f k x} ⊆ movingUpperLevelClosedTail f t N := by
  intro x hx
  apply subset_closure
  exact Set.mem_iUnion.mpr
    ⟨k, Set.mem_iUnion.mpr ⟨hk, hx⟩⟩

private theorem iInter_movingUpperLevelClosedTail_subset_of_eventual_open_upper
    {X : Type*} [TopologicalSpace X]
    (f : ℕ → X → ℝ) (g : X → ℝ)
    (hjoint : ∀ (x : X) (t : ℝ), g x < t →
      ∃ (N : ℕ) (U : Set X), IsOpen U ∧ x ∈ U ∧
        ∀ (k : ℕ), N ≤ k → ∀ y ∈ U, f k y < t)
    (t : ℝ) :
    (⋂ N : ℕ, movingUpperLevelClosedTail f t N) ⊆
      {x : X | t ≤ g x} := by
  intro x hx
  change t ≤ g x
  by_contra hnot
  have hlt : g x < t := lt_of_not_ge hnot
  obtain ⟨N, U, hU, hxU, hupper⟩ := hjoint x t hlt
  have hxclose : x ∈ movingUpperLevelClosedTail f t N :=
    Set.mem_iInter.mp hx N
  change x ∈ closure
    (⋃ k : ℕ, ⋃ (_ : N ≤ k), {y : X | t ≤ f k y}) at hxclose
  obtain ⟨y, hyU, hytail⟩ :=
    (mem_closure_iff.mp hxclose) U hU hxU
  obtain ⟨k, hyk⟩ := Set.mem_iUnion.mp hytail
  obtain ⟨hk, hylevel⟩ := Set.mem_iUnion.mp hyk
  exact (not_le_of_gt (hupper k hk y hyU)) hylevel

private theorem limsup_measureReal_moving_upperLevel_le_of_probability_tendsto
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    (μ : ProbabilityMeasure X) (μk : ℕ → ProbabilityMeasure X)
    (hμ : Tendsto μk atTop (𝓝 μ))
    (f : ℕ → X → ℝ) (g : X → ℝ)
    (hjoint : ∀ t : ℝ,
      (⋂ N : ℕ, movingUpperLevelClosedTail f t N) ⊆
        {x : X | t ≤ g x})
    (t : ℝ) :
    Filter.limsup
        (fun k : ℕ =>
          (μk k : Measure X).real {x : X | t ≤ f k x}) atTop ≤
      (μ : Measure X).real {x : X | t ≤ g x} := by
  let S : ℕ → Set X := movingUpperLevelClosedTail f t
  have hclosed (N : ℕ) : IsClosed (S N) :=
    isClosed_movingUpperLevelClosedTail f t N
  have hanti : Antitone S :=
    antitone_movingUpperLevelClosedTail f t
  have hcob :
      Filter.IsCoboundedUnder (· ≤ ·) atTop
        (fun k : ℕ =>
          (μk k : Measure X).real {x : X | t ≤ f k x}) :=
    Filter.isCoboundedUnder_le_of_le atTop fun _ =>
      measureReal_nonneg
  have htail (N : ℕ) :
      Filter.limsup
          (fun k : ℕ =>
            (μk k : Measure X).real {x : X | t ≤ f k x}) atTop ≤
        (μ : Measure X).real (S N) := by
    have hcompare : ∀ᶠ k : ℕ in atTop,
        (μk k : Measure X).real {x : X | t ≤ f k x} ≤
          (μk k : Measure X).real (S N) := by
      filter_upwards [eventually_ge_atTop N] with k hk
      exact measureReal_mono
        (moving_upperLevel_subset_closedTail f t hk)
    have hbounded :
        Filter.IsBoundedUnder (· ≤ ·) atTop
          (fun k : ℕ => (μk k : Measure X).real (S N)) :=
      Filter.isBoundedUnder_of_eventually_le
        (Filter.Eventually.of_forall fun _ => measureReal_le_one)
    exact (Filter.limsup_le_limsup hcompare hcob hbounded).trans
      (limsup_measureReal_closed_le_of_probability_tendsto
        μ μk hμ (hclosed N))
  have hmeasure :
      Tendsto
        (fun N : ℕ => (μ : Measure X).real (S N)) atTop
        (𝓝 ((μ : Measure X).real (⋂ N : ℕ, S N))) := by
    have hENN := tendsto_measure_iInter_atTop
      (μ := (μ : Measure X))
      (fun N : ℕ => (hclosed N).measurableSet.nullMeasurableSet)
      hanti ⟨0, measure_ne_top (μ : Measure X) (S 0)⟩
    simpa only [Measure.real, comp_def] using
      (ENNReal.tendsto_toReal
        (measure_ne_top (μ : Measure X)
          (⋂ N : ℕ, S N))).comp hENN
  have hlimit :
      Filter.limsup
          (fun k : ℕ =>
            (μk k : Measure X).real {x : X | t ≤ f k x}) atTop ≤
        (μ : Measure X).real (⋂ N : ℕ, S N) :=
    ge_of_tendsto hmeasure (Filter.Eventually.of_forall htail)
  exact hlimit.trans (measureReal_mono (hjoint t))

private theorem limsup_integral_moving_le_of_probability_tendsto
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    (μ : ProbabilityMeasure X) (μk : ℕ → ProbabilityMeasure X)
    (hμ : Tendsto μk atTop (𝓝 μ))
    (f : ℕ → X → ℝ) (g : X → ℝ) (C : ℝ)
    (hfmeas : ∀ k : ℕ, Measurable (f k))
    (hg : UpperSemicontinuous g)
    (hC : 0 ≤ C)
    (hfnonneg : ∀ (k : ℕ) (x : X), 0 ≤ f k x)
    (hfbound : ∀ (k : ℕ) (x : X), f k x ≤ C)
    (hgnonneg : ∀ x : X, 0 ≤ g x)
    (hgbound : ∀ x : X, g x ≤ C)
    (hjoint : ∀ t : ℝ,
      (⋂ N : ℕ, movingUpperLevelClosedTail f t N) ⊆
        {x : X | t ≤ g x}) :
    Filter.limsup
        (fun k : ℕ => ∫ x, f k x ∂(μk k : Measure X)) atTop ≤
      ∫ x, g x ∂(μ : Measure X) := by
  let ν : Measure ℝ :=
    (volume : Measure ℝ).restrict (Set.Ioc 0 C)
  let G : ℕ → ℝ → ℝ :=
    fun k t => (μk k : Measure X).real {x : X | t ≤ f k x}
  let h : ℝ → ℝ :=
    fun t => (μ : Measure X).real {x : X | t ≤ g x}
  have hGmeas (k : ℕ) : Measurable (G k) :=
    measurable_measureReal_upperLevel (μk k : Measure X) (f k)
  have hmeas : Measurable h :=
    measurable_measureReal_upperLevel (μ : Measure X) g
  have hhint : Integrable h ν := by
    refine (integrable_const (1 : ℝ)).mono'
      hmeas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun t => by
      dsimp [h]
      rw [abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
  have hGnonneg (k : ℕ) (t : ℝ) : 0 ≤ G k t :=
    measureReal_nonneg
  have hGbound (k : ℕ) (t : ℝ) : G k t ≤ 1 :=
    measureReal_le_one
  have hhpos : ∀ᵐ t ∂ν, 0 ≤ h t :=
    Filter.Eventually.of_forall fun _ => measureReal_nonneg
  have hlevel :
      ∀ᵐ t ∂ν,
        Filter.limsup (fun k : ℕ => G k t) atTop ≤ h t := by
    apply Filter.Eventually.of_forall
    intro t
    exact limsup_measureReal_moving_upperLevel_le_of_probability_tendsto
      μ μk hμ f g hjoint t
  have hgint := integrable_upperSemicontinuous_of_probability_bound
    μ hg hC hgnonneg hgbound
  have hfint (k : ℕ) : Integrable (f k) (μk k : Measure X) := by
    refine (integrable_const C).mono'
      (hfmeas k).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hfnonneg k x)] using hfbound k x
  calc
    Filter.limsup
        (fun k : ℕ => ∫ x, f k x ∂(μk k : Measure X)) atTop =
      Filter.limsup (fun k : ℕ => ∫ t, G k t ∂ν) atTop := by
        congr 1
        funext k
        exact (hfint k).integral_eq_integral_Ioc_meas_le
          (Filter.Eventually.of_forall (hfnonneg k))
          (Filter.Eventually.of_forall (hfbound k))
    _ ≤ ∫ t, h t ∂ν :=
      ActualJetPlurisubharmonicClosure.limsup_integral_le_of_nonnegative_bounded
        ν G h 1 hGmeas hhint hGnonneg hGbound hhpos hlevel
    _ = ∫ x, g x ∂(μ : Measure X) :=
      (hgint.integral_eq_integral_Ioc_meas_le
        (Filter.Eventually.of_forall hgnonneg)
        (Filter.Eventually.of_forall hgbound)).symm

private theorem limsup_integral_moving_le_of_probability_tendsto_and_eventual_open_upper
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    (μ : ProbabilityMeasure X) (μk : ℕ → ProbabilityMeasure X)
    (hμ : Tendsto μk atTop (𝓝 μ))
    (f : ℕ → X → ℝ) (g : X → ℝ) (C : ℝ)
    (hfmeas : ∀ k : ℕ, Measurable (f k))
    (hg : UpperSemicontinuous g)
    (hC : 0 ≤ C)
    (hfnonneg : ∀ (k : ℕ) (x : X), 0 ≤ f k x)
    (hfbound : ∀ (k : ℕ) (x : X), f k x ≤ C)
    (hgnonneg : ∀ x : X, 0 ≤ g x)
    (hgbound : ∀ x : X, g x ≤ C)
    (hjoint : ∀ (x : X) (t : ℝ), g x < t →
      ∃ (N : ℕ) (U : Set X), IsOpen U ∧ x ∈ U ∧
        ∀ (k : ℕ), N ≤ k → ∀ y ∈ U, f k y < t) :
    Filter.limsup
        (fun k : ℕ => ∫ x, f k x ∂(μk k : Measure X)) atTop ≤
      ∫ x, g x ∂(μ : Measure X) := by
  apply limsup_integral_moving_le_of_probability_tendsto
    μ μk hμ f g C hfmeas hg hC
      hfnonneg hfbound hgnonneg hgbound
  exact iInter_movingUpperLevelClosedTail_subset_of_eventual_open_upper
    f g hjoint

end BergmanJetPortmanteauMovingUpperTailBridge

namespace TorusHomogeneousBrascampLieb

open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert WeightedBrascampLieb WeightedResolventConstantCore
open EqualitySaturatingKillingPaths ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity
open MatrixTorusBochnerIdentity MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault WeightedTorusBrascampLieb
open MatrixTorusDolbeaultGraph TorusDeckGraphAdjoint TorusFriedrichsCutoff
open RadialPhysicalVelocityCompactGraph RadialPhysicalInverseSquareRootEnergy
open RadialPhysicalResolventRootCutoffPairing RadialPhysicalResolventDefectReduction
open TorusHomogeneousWeakResolventRootCoercivity
open scoped BigOperators ENNReal ComplexConjugate ComplexOrder
  MatrixOrder InnerProductSpace Topology ContDiff

private def angularSourceFreeScalarRadialGraphTest
    {n : ℕ} (U : LogSpace n → ℂ) (m : ℕ) (z : LogSpace n) : ℂ :=
  complexSourceCoverRadialCutoff m z * U z

private theorem contDiff_angularSourceFreeScalarRadialGraphTest
    {n : ℕ} {U : LogSpace n → ℂ}
    (hU : ContDiff ℝ 3 U) (m : ℕ) :
    ContDiff ℝ 3 (angularSourceFreeScalarRadialGraphTest U m) := by
  exact (contDiff_complexSourceCoverRadialCutoff_all m 3).mul hU

private theorem angularSourceFreeScalarRadialGraphTest_periodic
    {n : ℕ} {U : LogSpace n → ℂ}
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (m : ℕ) (d : Fin n → ℤ) :
    Function.Periodic
      (angularSourceFreeScalarRadialGraphTest U m)
      (imaginaryShift d) := by
  intro z
  unfold angularSourceFreeScalarRadialGraphTest
  rw [complexSourceCoverRadialCutoff_periodic m d z, hperiod d z]

private theorem torusScalarRepresentative_angularSourceFreeScalarRadialGraphTest
    {n : ℕ} (U : LogSpace n → ℂ) (m : ℕ) (q : LogTorus n) :
    torusScalarRepresentative
      (angularSourceFreeScalarRadialGraphTest U m) q =
      (sourceRadialCutoff m q : ℂ) * torusScalarRepresentative U q := by
  unfold angularSourceFreeScalarRadialGraphTest
  rw [torusScalarRepresentative_mul,
    torusScalarRepresentative_complexSourceCoverRadialCutoff]

private theorem hasCompactSupport_angularSourceFreeScalarRadialGraphTest
    {n : ℕ} (U : LogSpace n → ℂ) (m : ℕ) :
    HasCompactSupport
      (torusScalarRepresentative
        (angularSourceFreeScalarRadialGraphTest U m)) := by
  have heq :
      torusScalarRepresentative
        (angularSourceFreeScalarRadialGraphTest U m) =
      fun q : LogTorus n =>
        (sourceRadialCutoff m q : ℂ) * torusScalarRepresentative U q := by
    funext q
    exact torusScalarRepresentative_angularSourceFreeScalarRadialGraphTest
      U m q
  rw [heq]
  exact (complexSourceRadialCutoff_hasCompactSupport m).mul_right

private theorem angularSourceFreeScalarRadialGraphTest_scalar_memLp
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (m : ℕ) :
    MemLp
      (torusScalarRepresentative
        (angularSourceFreeScalarRadialGraphTest U m)) 2
      (angularWeightedTorusMeasure a) := by
  let : IsLocallyFiniteMeasure (angularWeightedTorusMeasure a) :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  have : IsFiniteMeasureOnCompacts (angularWeightedTorusMeasure a) :=
    isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  apply (continuous_torusScalarRepresentative_of_periodic
    (contDiff_angularSourceFreeScalarRadialGraphTest hU m).continuous
    (angularSourceFreeScalarRadialGraphTest_periodic hperiod m)).memLp_of_hasCompactSupport
  exact hasCompactSupport_angularSourceFreeScalarRadialGraphTest U m

private theorem angularSourceFreeScalarRadialGraphTest_barPartial_memLp
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (m : ℕ) :
    MemLp
      (torusFunctionBarPartialRepresentative
        (angularSourceFreeScalarRadialGraphTest U m)) 2
      (angularWeightedTorusMeasure a) := by
  let : IsLocallyFiniteMeasure (angularWeightedTorusMeasure a) :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  have : IsFiniteMeasureOnCompacts (angularWeightedTorusMeasure a) :=
    isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  let V : LogSpace n → ℂ := angularSourceFreeScalarRadialGraphTest U m
  have hVp : ∀ d : Fin n → ℤ,
      Function.Periodic V (imaginaryShift d) :=
    angularSourceFreeScalarRadialGraphTest_periodic hperiod m
  apply (continuous_torusFunctionBarPartialRepresentative_of_periodic
    ((contDiff_angularSourceFreeScalarRadialGraphTest hU m).of_le
      (by norm_num)) hVp).memLp_of_hasCompactSupport
  exact hasCompactSupport_torusFunctionBarPartialRepresentative_of_periodic
    V hVp (hasCompactSupport_angularSourceFreeScalarRadialGraphTest U m)

private def angularSourceFreeScalarCutoffGradient
    {n : ℕ} (U : LogSpace n → ℂ)
    (m : ℕ) (q : LogTorus n) : EuclideanSpace ℂ (Fin n) :=
  torusScalarRepresentative U q • sourceCutoffBarGradient m q

private theorem continuous_angularSourceFreeScalarCutoffGradient
    {n : ℕ} {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (m : ℕ) :
    Continuous (angularSourceFreeScalarCutoffGradient U m) := by
  exact (continuous_torusScalarRepresentative_of_periodic
    hU.continuous hperiod).smul (continuous_sourceCutoffBarGradient m)

private theorem angularSourceFreeScalarCutoffGradient_norm_le
    {n : ℕ} (U : LogSpace n → ℂ)
    {C : ℝ}
    (hC : ∀ x : Space n,
      ‖euclideanGradient (fun y : Space n => unitBump y) x‖ ≤ C)
    (m : ℕ) (q : LogTorus n) :
    ‖angularSourceFreeScalarCutoffGradient U m q‖ ≤
      (((m : ℝ) + 1)⁻¹ * C) * ‖torusScalarRepresentative U q‖ := by
  unfold angularSourceFreeScalarCutoffGradient
  rw [norm_smul]
  calc
    ‖torusScalarRepresentative U q‖ * ‖sourceCutoffBarGradient m q‖ ≤
      ‖torusScalarRepresentative U q‖ * (((m : ℝ) + 1)⁻¹ * C) :=
      mul_le_mul_of_nonneg_left
        (sourceCutoffBarGradient_norm_le hC m q) (norm_nonneg _)
    _ = _ := by ring

private theorem angularSourceFreeScalarCutoffGradient_memLp
    {n : ℕ} {a : LogTorus n → ℝ}
    {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (hu : MemLp (torusScalarRepresentative U) 2
      (angularWeightedTorusMeasure a))
    (m : ℕ) :
    MemLp (angularSourceFreeScalarCutoffGradient U m) 2
      (angularWeightedTorusMeasure a) := by
  obtain ⟨C, _, hC⟩ := unitBump_euclideanGradient_bound (n := n)
  apply hu.of_le_mul (c := ((m : ℝ) + 1)⁻¹ * C)
    (continuous_angularSourceFreeScalarCutoffGradient
      hU hperiod m).aestronglyMeasurable
  filter_upwards [] with q
  exact angularSourceFreeScalarCutoffGradient_norm_le U hC m q

private theorem angularSourceFreeScalarCutoffGradient_L2_norm_le
    {n : ℕ} {a : LogTorus n → ℝ}
    {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (hu : MemLp (torusScalarRepresentative U) 2
      (angularWeightedTorusMeasure a))
    {C : ℝ} (hCnonneg : 0 ≤ C)
    (hC : ∀ x : Space n,
      ‖euclideanGradient (fun y : Space n => unitBump y) x‖ ≤ C)
    (m : ℕ) :
    ‖(angularSourceFreeScalarCutoffGradient_memLp hU hperiod hu m).toLp
      (angularSourceFreeScalarCutoffGradient U m)‖ ≤
      (((m : ℝ) + 1)⁻¹ * C) *
        ‖hu.toLp (torusScalarRepresentative U)‖ := by
  apply complexLp_norm_le_of_ae_norm_le
    (angularSourceFreeScalarCutoffGradient_memLp hU hperiod hu m) hu
    (mul_nonneg (by positivity) hCnonneg)
  filter_upwards [] with q
  exact angularSourceFreeScalarCutoffGradient_norm_le U hC m q

private theorem angularSourceFreeScalarCutoffGradient_L2_tendsto_zero
    {n : ℕ} {a : LogTorus n → ℝ}
    {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (hu : MemLp (torusScalarRepresentative U) 2
      (angularWeightedTorusMeasure a)) :
    Tendsto
      (fun m : ℕ =>
        (angularSourceFreeScalarCutoffGradient_memLp
          hU hperiod hu m).toLp
            (angularSourceFreeScalarCutoffGradient U m))
      atTop (nhds (0 : angularWeightedFormL2 a)) := by
  obtain ⟨C, hCnonneg, hC⟩ :=
    unitBump_euclideanGradient_bound (n := n)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun m => norm_nonneg _)
    (fun m => angularSourceFreeScalarCutoffGradient_L2_norm_le
      hU hperiod hu hCnonneg hC m)
  have hz := inv_nat_add_one_tendsto_zero.mul_const
    (C * ‖hu.toLp (torusScalarRepresentative U)‖)
  simpa only [Lp.norm_toLp, mul_assoc, zero_mul] using hz

private theorem torusFunctionBarPartialRepresentative_angularSourceFreeScalarRadialGraphTest
    {n : ℕ} {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (m : ℕ) (q : LogTorus n) :
    torusFunctionBarPartialRepresentative
      (angularSourceFreeScalarRadialGraphTest U m) q =
      (sourceRadialCutoff m q : ℂ) •
        torusFunctionBarPartialRepresentative U q +
      angularSourceFreeScalarCutoffGradient U m q := by
  ext j
  change
    sourceTorusBarPartial
      (angularSourceFreeScalarRadialGraphTest U m) j q =
      (sourceRadialCutoff m q : ℂ) *
        sourceTorusBarPartial U j q +
      torusScalarRepresentative U q *
        sourceTorusBarPartial (complexSourceCoverRadialCutoff m) j q
  have hprod :
      (fun z : LogSpace n =>
        barPartialCoordinate
          (angularSourceFreeScalarRadialGraphTest U m) z j) =
      fun z : LogSpace n =>
        complexSourceCoverRadialCutoff m z *
            barPartialCoordinate U z j +
          U z *
            barPartialCoordinate
              (complexSourceCoverRadialCutoff m) z j := by
    funext z
    unfold angularSourceFreeScalarRadialGraphTest
    rw [barPartial_mul
      (contDiff_complexSourceCoverRadialCutoff_all m 1)
      (hU.of_le (by norm_num)) z j]
    ring
  unfold sourceTorusBarPartial
  change torusScalarRepresentative
    (fun z : LogSpace n =>
      barPartialCoordinate
        (angularSourceFreeScalarRadialGraphTest U m) z j) q = _
  rw [hprod, torusScalarRepresentative_add,
    torusScalarRepresentative_mul, torusScalarRepresentative_mul,
    torusScalarRepresentative_complexSourceCoverRadialCutoff]

private theorem angularSourceFreeScalarRadialGraphTest_scalar_L2_tendsto
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (hu : MemLp (torusScalarRepresentative U) 2
      (angularWeightedTorusMeasure a)) :
    Tendsto
      (fun m : ℕ =>
        angularScalarL2OfRepresentative a
          (angularSourceFreeScalarRadialGraphTest U m)
          (angularSourceFreeScalarRadialGraphTest_scalar_memLp
            ha hU hperiod m))
      atTop (nhds (hu.toLp (torusScalarRepresentative U))) := by
  have hcut := angularSourceRadialCutoff_smul_L2_tendsto hu
  apply Filter.Tendsto.congr' _ hcut
  filter_upwards [] with m
  unfold angularScalarL2OfRepresentative
  apply MemLp.toLp_congr
  filter_upwards [] with q
  rw [torusScalarRepresentative_angularSourceFreeScalarRadialGraphTest]
  simp only [smul_eq_mul]

private def angularSourceFreeInverseRootGradientField
    {n : ℕ} (a : LogTorus n → ℝ)
    (U : LogSpace n → ℂ) (q : LogTorus n) :
    EuclideanSpace ℂ (Fin n) :=
  Matrix.toEuclideanLin
    ((angularMatrixSquareRoot
      (angularTorusComplexHessianMatrix a) q)⁻¹)
    (angularEuclideanConjugation
      (torusFunctionBarPartialRepresentative U q))

private def angularSourceFreeInverseRootGradientL2
    {n : ℕ} {a : LogTorus n → ℝ}
    {U : LogSpace n → ℂ}
    (hr : MemLp (angularSourceFreeInverseRootGradientField a U)
      2 (angularWeightedTorusMeasure a)) :
    angularWeightedFormL2 a :=
  hr.toLp (angularSourceFreeInverseRootGradientField a U)

private def angularSourceFreeTruncatedGradientL2
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (hu : MemLp (torusScalarRepresentative U) 2
      (angularWeightedTorusMeasure a))
    (m : ℕ) : angularWeightedFormL2 a :=
  angularBarPartialL2OfRepresentative a
    (angularSourceFreeScalarRadialGraphTest U m)
    (angularSourceFreeScalarRadialGraphTest_barPartial_memLp
      ha hU hperiod m) -
  (angularSourceFreeScalarCutoffGradient_memLp hU hperiod hu m).toLp
    (angularSourceFreeScalarCutoffGradient U m)

private theorem angularSourceFreeTruncatedGradientL2_ae_eq
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (hu : MemLp (torusScalarRepresentative U) 2
      (angularWeightedTorusMeasure a)) (m : ℕ) :
    (fun q : LogTorus n =>
      angularSourceFreeTruncatedGradientL2 ha hU hperiod hu m q) =ᵐ[
        angularWeightedTorusMeasure a]
    (fun q : LogTorus n =>
      (sourceRadialCutoff m q : ℂ) •
        torusFunctionBarPartialRepresentative U q) := by
  let V : LogSpace n → ℂ := angularSourceFreeScalarRadialGraphTest U m
  let hD := angularSourceFreeScalarRadialGraphTest_barPartial_memLp
    ha hU hperiod m
  let hC := angularSourceFreeScalarCutoffGradient_memLp
    hU hperiod hu m
  let A : angularWeightedFormL2 a :=
    angularBarPartialL2OfRepresentative a V hD
  let B : angularWeightedFormL2 a :=
    hC.toLp (angularSourceFreeScalarCutoffGradient U m)
  change (fun q : LogTorus n => (A - B) q) =ᵐ[
    angularWeightedTorusMeasure a] _
  filter_upwards [MeasureTheory.Lp.coeFn_sub A B,
    hD.coeFn_toLp, hC.coeFn_toLp] with q hsub hder hcomm
  rw [hsub]
  change
    (hD.toLp (torusFunctionBarPartialRepresentative V)) q -
      (hC.toLp (angularSourceFreeScalarCutoffGradient U m)) q = _
  rw [hder, hcomm,
    torusFunctionBarPartialRepresentative_angularSourceFreeScalarRadialGraphTest
      hU m q]
  simp only [Complex.coe_smul, add_sub_cancel_right]

private theorem angularSourceFreeTruncatedGradientL2_resolvent_pairing
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (hu : MemLp (torusScalarRepresentative U) 2
      (angularWeightedTorusMeasure a))
    (m : ℕ) (g : angularWeightedScalarL2 a) :
    @inner ℂ (angularWeightedFormL2 a) _
      (WithLp.snd
        (angularWeakDolbeaultResolvent a g :
          angularDolbeaultGraphAmbient a))
      (angularSourceFreeTruncatedGradientL2
        ha hU hperiod hu m) =
    @inner ℂ (angularWeightedScalarL2 a) _
      (g - angularWeakScalarResolventCLM a g)
      (angularScalarL2OfRepresentative a
        (angularSourceFreeScalarRadialGraphTest U m)
        (angularSourceFreeScalarRadialGraphTest_scalar_memLp
          ha hU hperiod m)) -
    @inner ℂ (angularWeightedFormL2 a) _
      (WithLp.snd
        (angularWeakDolbeaultResolvent a g :
          angularDolbeaultGraphAmbient a))
      ((angularSourceFreeScalarCutoffGradient_memLp
        hU hperiod hu m).toLp
          (angularSourceFreeScalarCutoffGradient U m)) := by
  unfold angularSourceFreeTruncatedGradientL2
  rw [inner_sub_right]
  rw [angularWeakDolbeaultResolvent_smoothGraphTest_adjoint a g
    (angularSourceFreeScalarRadialGraphTest U m)
    (contDiff_angularSourceFreeScalarRadialGraphTest hU m)
    (angularSourceFreeScalarRadialGraphTest_periodic hperiod m)
    (hasCompactSupport_angularSourceFreeScalarRadialGraphTest U m)
    (angularSourceFreeScalarRadialGraphTest_scalar_memLp
      ha hU hperiod m)
    (angularSourceFreeScalarRadialGraphTest_barPartial_memLp
      ha hU hperiod m)]

private theorem tendsto_angularSourceFreeTruncatedGradient_resolvent_pairing
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (hu : MemLp (torusScalarRepresentative U) 2
      (angularWeightedTorusMeasure a))
    (g : angularWeightedScalarL2 a) :
    Tendsto
      (fun m : ℕ =>
        @inner ℂ (angularWeightedFormL2 a) _
          (WithLp.snd
            (angularWeakDolbeaultResolvent a g :
              angularDolbeaultGraphAmbient a))
          (angularSourceFreeTruncatedGradientL2 ha hU hperiod hu m))
      atTop
      (nhds
        (@inner ℂ (angularWeightedScalarL2 a) _
          (g - angularWeakScalarResolventCLM a g)
          (hu.toLp (torusScalarRepresentative U)))) := by
  let W : angularWeightedFormL2 a :=
    WithLp.snd
      (angularWeakDolbeaultResolvent a g :
        angularDolbeaultGraphAmbient a)
  let d : angularWeightedScalarL2 a :=
    g - angularWeakScalarResolventCLM a g
  have hfirst :
      Tendsto
        (fun m : ℕ =>
          @inner ℂ (angularWeightedScalarL2 a) _ d
            (angularScalarL2OfRepresentative a
              (angularSourceFreeScalarRadialGraphTest U m)
              (angularSourceFreeScalarRadialGraphTest_scalar_memLp
                ha hU hperiod m)))
        atTop
        (nhds
          (@inner ℂ (angularWeightedScalarL2 a) _ d
            (hu.toLp (torusScalarRepresentative U)))) :=
    tendsto_const_nhds.inner
      (angularSourceFreeScalarRadialGraphTest_scalar_L2_tendsto
        ha hU hperiod hu)
  have hsecond :
      Tendsto
        (fun m : ℕ =>
          @inner ℂ (angularWeightedFormL2 a) _ W
            ((angularSourceFreeScalarCutoffGradient_memLp
              hU hperiod hu m).toLp
                (angularSourceFreeScalarCutoffGradient U m)))
        atTop (nhds (0 : ℂ)) := by
    simpa only [inner_zero_right] using tendsto_const_nhds.inner
      (angularSourceFreeScalarCutoffGradient_L2_tendsto_zero
        hU hperiod hu)
  have hlimit := hfirst.sub hsecond
  simp only [sub_zero] at hlimit
  apply Filter.Tendsto.congr' _ hlimit
  filter_upwards [] with m
  exact (angularSourceFreeTruncatedGradientL2_resolvent_pairing
    ha hU hperiod hu m g).symm

private theorem angularSourceFreeTruncatedGradient_root_pairing
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (hu : MemLp (torusScalarRepresentative U) 2
      (angularWeightedTorusMeasure a))
    (hr : MemLp (angularSourceFreeInverseRootGradientField a U)
      2 (angularWeightedTorusMeasure a))
    (W : angularWeightedFormL2 a) (m : ℕ) :
    @inner ℂ (angularWeightedFormL2 a) _ W
      (angularSourceFreeTruncatedGradientL2
        ha hU hperiod hu m) =
    @inner ℂ (angularWeightedFormL2 a) _
      (angularSourceFreeInverseRootGradientL2 hr)
      (angularPhysicalResolventRootCutoffL2 ha2 hH W m) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [angularSourceFreeTruncatedGradientL2_ae_eq
      ha hU hperiod hu m,
     hr.coeFn_toLp,
     (angularPhysicalResolventRootCutoffField_memLp
       ha2 hH W m).coeFn_toLp]
      with q hrow hinv hroot
  change
    @inner ℂ (EuclideanSpace ℂ (Fin n)) _ (W q)
      (angularSourceFreeTruncatedGradientL2
        ha hU hperiod hu m q) =
    @inner ℂ (EuclideanSpace ℂ (Fin n)) _
      (angularSourceFreeInverseRootGradientL2 hr q)
      (angularPhysicalResolventRootCutoffL2 ha2 hH W m q)
  rw [hrow]
  change
    @inner ℂ (EuclideanSpace ℂ (Fin n)) _ (W q)
      ((sourceRadialCutoff m q : ℂ) •
        torusFunctionBarPartialRepresentative U q) =
    @inner ℂ (EuclideanSpace ℂ (Fin n)) _
      (hr.toLp (angularSourceFreeInverseRootGradientField a U) q)
      ((angularPhysicalResolventRootCutoffField_memLp
        ha2 hH W m).toLp
          (angularPhysicalResolventRootCutoffField a W m) q)
  rw [hinv, hroot]
  unfold angularPhysicalResolventRootCutoffField
    angularSourceFreeInverseRootGradientField
  rw [inner_smul_right, inner_smul_right]
  congr 1
  change
    @inner ℂ (EuclideanSpace ℂ (Fin n)) _ (W q)
      (torusFunctionBarPartialRepresentative U q) =
    @inner ℂ (EuclideanSpace ℂ (Fin n)) _
      (Matrix.toEuclideanLin
        ((CFC.sqrt (angularTorusComplexHessianMatrix a q))⁻¹)
        (WithLp.toLp 2
          (star (fun i => torusFunctionBarPartialRepresentative U q i))))
      (Matrix.toEuclideanLin
        (CFC.sqrt (angularTorusComplexHessianMatrix a q))
        (angularEuclideanConjugation (W q)))
  rw [complexPositiveInverseSquareRootAction_pairing
    (hH q)
    (fun i => torusFunctionBarPartialRepresentative U q i)
    (angularEuclideanConjugation (W q)),
    EuclideanSpace.inner_eq_star_dotProduct]
  rfl

private theorem tendsto_angularSourceFreeResolventRootCutoff_pairing
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (hu : MemLp (torusScalarRepresentative U) 2
      (angularWeightedTorusMeasure a))
    (hr : MemLp (angularSourceFreeInverseRootGradientField a U)
      2 (angularWeightedTorusMeasure a))
    (g : angularWeightedScalarL2 a) :
    Tendsto
      (fun m : ℕ =>
        @inner ℂ (angularWeightedFormL2 a) _
          (angularSourceFreeInverseRootGradientL2 hr)
          (angularPhysicalResolventRootCutoffL2 ha2 hH
            (WithLp.snd
              (angularWeakDolbeaultResolvent a g :
                angularDolbeaultGraphAmbient a)) m))
      atTop
      (nhds
        (@inner ℂ (angularWeightedScalarL2 a) _
          (g - angularWeakScalarResolventCLM a g)
          (hu.toLp (torusScalarRepresentative U)))) := by
  apply Filter.Tendsto.congr' _
    (tendsto_angularSourceFreeTruncatedGradient_resolvent_pairing
      ha hU hperiod hu g)
  filter_upwards [] with m
  exact angularSourceFreeTruncatedGradient_root_pairing
    ha ha2 hH hU hperiod hu hr
    (WithLp.snd
      (angularWeakDolbeaultResolvent a g :
        angularDolbeaultGraphAmbient a)) m

private theorem angularSourceFreeResolventDefectPairingBound
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (ha3 : ContDiff ℝ 3 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (hu : MemLp (torusScalarRepresentative U) 2
      (angularWeightedTorusMeasure a))
    (hr : MemLp (angularSourceFreeInverseRootGradientField a U)
      2 (angularWeightedTorusMeasure a))
    (g : angularWeightedScalarL2 a) :
    ‖@inner ℂ (angularWeightedScalarL2 a) _
      (hu.toLp (torusScalarRepresentative U))
      (g - angularWeakScalarResolventCLM a g)‖ ≤
    ‖angularSourceFreeInverseRootGradientL2 hr‖ *
      ‖g - angularWeakScalarResolventCLM a g‖ := by
  let ha2 : ContDiff ℝ 2 (angularCoverPotential a) :=
    ha3.of_le (by norm_num)
  let W : angularWeightedFormL2 a :=
    WithLp.snd
      (angularWeakDolbeaultResolvent a g :
        angularDolbeaultGraphAmbient a)
  let d : angularWeightedScalarL2 a :=
    g - angularWeakScalarResolventCLM a g
  let r : angularWeightedFormL2 a :=
    angularSourceFreeInverseRootGradientL2 hr
  let f : angularWeightedScalarL2 a :=
    hu.toLp (torusScalarRepresentative U)
  change ‖@inner ℂ (angularWeightedScalarL2 a) _ f d‖ ≤
    ‖r‖ * ‖d‖
  rw [norm_inner_symm]
  have hlim :
      Tendsto
        (fun m : ℕ =>
          @inner ℂ (angularWeightedFormL2 a) _ r
            (angularPhysicalResolventRootCutoffL2 ha2 hH W m))
        atTop
        (nhds (@inner ℂ (angularWeightedScalarL2 a) _ d f)) :=
    tendsto_angularSourceFreeResolventRootCutoff_pairing
      ha ha2 hH hU hperiod hu hr g
  have hnorm :
      Tendsto
        (fun m : ℕ =>
          ‖@inner ℂ (angularWeightedFormL2 a) _ r
            (angularPhysicalResolventRootCutoffL2 ha2 hH W m)‖)
        atTop
        (nhds ‖@inner ℂ (angularWeightedScalarL2 a) _ d f‖) :=
    (continuous_norm.tendsto _).comp hlim
  apply le_of_tendsto' hnorm
  intro m
  exact (norm_inner_le_norm r
    (angularPhysicalResolventRootCutoffL2 ha2 hH W m)).trans
      (mul_le_mul_of_nonneg_left
        (angularPhysicalWeakResolventRootCutoffCoercivity
          ha ha3 hH g m)
        (norm_nonneg r))

private theorem angularSourceFreeBrascampLieb_of_mem_resolventDefect_closure
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (ha3 : ContDiff ℝ 3 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (hu : MemLp (torusScalarRepresentative U) 2
      (angularWeightedTorusMeasure a))
    (hr : MemLp (angularSourceFreeInverseRootGradientField a U)
      2 (angularWeightedTorusMeasure a))
    (hclosure :
      hu.toLp (torusScalarRepresentative U) ∈
        ((ContinuousLinearMap.id ℂ (angularWeightedScalarL2 a) -
          angularWeakScalarResolventCLM a).range).topologicalClosure) :
    ‖hu.toLp (torusScalarRepresentative U)‖ ≤
      ‖angularSourceFreeInverseRootGradientL2 hr‖ := by
  let f : angularWeightedScalarL2 a :=
    hu.toLp (torusScalarRepresentative U)
  let r : angularWeightedFormL2 a :=
    angularSourceFreeInverseRootGradientL2 hr
  let T : angularWeightedScalarL2 a →L[ℂ]
      angularWeightedScalarL2 a :=
    ContinuousLinearMap.id ℂ (angularWeightedScalarL2 a) -
      angularWeakScalarResolventCLM a
  change ‖f‖ ≤ ‖r‖
  have hf : f ∈ closure (T.range : Set (angularWeightedScalarL2 a)) :=
    hclosure
  apply complexHilbert_norm_le_of_mem_closure_inner_bound
    f (T.range : Set (angularWeightedScalarL2 a)) hf (norm_nonneg r)
  intro v hv
  obtain ⟨g, rfl⟩ := hv
  change
    ‖@inner ℂ (angularWeightedScalarL2 a) _ f
      (g - angularWeakScalarResolventCLM a g)‖ ≤
      ‖r‖ * ‖g - angularWeakScalarResolventCLM a g‖
  exact angularSourceFreeResolventDefectPairingBound
    ha ha3 hH hU hperiod hu hr g

end TorusHomogeneousBrascampLieb

namespace BergmanJetHolomorphicPhysicalSupport

open Set Function Filter MeasureTheory Metric Matrix
open TorusCharacters WeightedTorusHilbert BergmanDiagonalBasisIndependence
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeRightDerivative JetEnvelopeTrueRadialMollifier
open EnvelopeSmoothing EnvelopeGeneralTorusDescent RadialPartitionBounds MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation MomentWeakBergman BergmanJetJointHolomorphicClosure
open BergmanJetJointHolomorphicPlurisubharmonicSmoothing BergmanJetSpatialSmoothing
open BergmanJetStrictRadialRegularizer BergmanJetJointHolomorphicStrictSchur
open BergmanJetHolomorphicPhysicalMeasure WeightedTorusDolbeault WeightedTorusBrascampLieb
open ArbitraryBodyOneSidedAngularResolventDefect
open scoped BigOperators ENNReal Topology ContDiff Convolution

private def momentWeakHolomorphicJointMollifierSupportError
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (q : SourceJointComplexCover n) : ℝ :=
  Real.log
      (finiteEnergySourcePartition F /
        normalizedVolume K.carrier) +
    BodyScale.canonicalScale K + 1 +
    BodyScale.canonicalScale K *
      (|sourceJointCoverTime q| + ‖sourceJointRealTimeCLM n‖) +
    ((n : ℝ) * LaurentJetSeparatedness.bodyRadius K) * 2

private theorem momentWeakHolomorphicJointMollification_le_support_add
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    (q : SourceJointComplexCover n) :
    momentWeakHolomorphicJointTrueRadialMollification
      K F htransport p k q ≤
      SupportFunction.supportFunction K.carrier
        (realLogCoordinate q.1) +
      momentWeakHolomorphicJointMollifierSupportError K F q := by
  let C : ℝ :=
    SupportFunction.supportFunction K.carrier
        (realLogCoordinate q.1) +
      momentWeakHolomorphicJointMollifierSupportError K F q
  have hleft : Integrable
      (fun y : SourceJointComplexCover n =>
        sourceJointTrueRadialMollifier n k y *
          momentWeakJointCoverUpperEnvelope
            K F htransport p (q - y))
      (volume : Measure (SourceJointComplexCover n)) :=
    integrable_sourceJointTrueRadialMollifier_mul_translate
      (locallyIntegrable_momentWeakJointCoverUpperEnvelope
        K F htransport p) k q
  have hright : Integrable
      (fun y : SourceJointComplexCover n =>
        sourceJointTrueRadialMollifier n k y * C)
      (volume : Measure (SourceJointComplexCover n)) :=
    (integrable_sourceJointTrueRadialMollifier n k).mul_const C
  change _ ≤ C
  unfold momentWeakHolomorphicJointTrueRadialMollification
    sourceJointTrueRadialSmoothed
  rw [MeasureTheory.convolution_def]
  calc
    (∫ y : SourceJointComplexCover n,
      sourceJointTrueRadialMollifier n k y *
        momentWeakJointCoverUpperEnvelope
          K F htransport p (q - y)) ≤
      ∫ y : SourceJointComplexCover n,
        sourceJointTrueRadialMollifier n k y * C := by
      apply MeasureTheory.integral_mono hleft hright
      intro y
      by_cases hy : sourceJointTrueRadialMollifier n k y = 0
      · simp only [hy, zero_mul, Std.le_refl]
      · apply mul_le_mul_of_nonneg_left _
          (sourceJointTrueRadialMollifier_nonneg n k y)
        have hball :=
          support_sourceJointTrueRadialMollifier_subset_closedBall k hy
        have hynorm : ‖y‖ ≤ (1 : ℝ) := by
          have hsmall :
              ‖y‖ ≤ 1 / ((k + 1 : ℕ) : ℝ) := by
            simpa only [Nat.cast_add, Nat.cast_one, one_div, mem_closedBall, dist_zero_right]
              using hball
          have hk : 0 < ((k + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.zero_lt_succ k
          have hradius : 1 / ((k + 1 : ℕ) : ℝ) ≤ 1 := by
            apply (div_le_iff₀ hk).mpr
            norm_num
          exact hsmall.trans hradius
        have hyfst : ‖y.1‖ ≤ (1 : ℝ) :=
          (norm_fst_le y).trans hynorm
        have hnR :
            0 ≤ (n : ℝ) *
              LaurentJetSeparatedness.bodyRadius K :=
          mul_nonneg (Nat.cast_nonneg n)
            (LaurentJetSeparatedness.bodyRadius_pos K).le
        have hsupport :
            SupportFunction.supportFunction K.carrier
              (realLogCoordinate (q - y).1) ≤
            SupportFunction.supportFunction K.carrier
              (realLogCoordinate q.1) +
              ((n : ℝ) *
                LaurentJetSeparatedness.bodyRadius K) * 2 := by
          calc
            SupportFunction.supportFunction K.carrier
                (realLogCoordinate (q - y).1) =
              SupportFunction.supportFunction K.carrier
                (realLogCoordinate (q.1 - y.1)) := rfl
            _ ≤ SupportFunction.supportFunction K.carrier
                  (realLogCoordinate q.1) +
                ((n : ℝ) *
                    LaurentJetSeparatedness.bodyRadius K) *
                  (2 * ‖y.1‖) :=
              supportFunction_realLogCoordinate_sub_le K
                (LaurentJetSeparatedness.bodyRadius_pos K).le
                (fun u hu =>
                  LaurentJetSeparatedness.norm_le_bodyRadius
                    K u hu)
                q.1 y.1
            _ ≤ SupportFunction.supportFunction K.carrier
                  (realLogCoordinate q.1) +
                ((n : ℝ) *
                    LaurentJetSeparatedness.bodyRadius K) *
                  2 := by
              have htwo : (2 : ℝ) * ‖y.1‖ ≤ 2 := by
                linarith
              exact add_le_add (le_refl _)
                (mul_le_mul_of_nonneg_left htwo hnR)
        have htime :
            |sourceJointCoverTime (q - y)| ≤
              |sourceJointCoverTime q| +
                ‖sourceJointRealTimeCLM n‖ := by
          calc
            |sourceJointCoverTime (q - y)| ≤
                |sourceJointCoverTime q| +
                  ‖sourceJointRealTimeCLM n‖ * ‖y‖ :=
              abs_sourceJointCoverTime_sub_le q y
            _ ≤ |sourceJointCoverTime q| +
                ‖sourceJointRealTimeCLM n‖ := by
              exact add_le_add (le_refl _)
                (mul_le_of_le_one_right
                  (norm_nonneg (sourceJointRealTimeCLM n)) hynorm)
        have hmax :
            max (sourceJointCoverTime (q - y)) 0 ≤
              |sourceJointCoverTime q| +
                ‖sourceJointRealTimeCLM n‖ := by
          apply max_le
          · exact (le_abs_self _).trans htime
          · exact add_nonneg (abs_nonneg _) (norm_nonneg _)
        have hnormpot :=
          momentNormalizedPotential_le_support_add
            F (realLogCoordinate (q - y).1)
        have hscale := BodyScale.canonicalScale_pos K
        have hscaled := mul_le_mul_of_nonneg_left hmax hscale.le
        change
          SupportFunction.supportFunction K.carrier
              (realLogCoordinate (q.1 - y.1)) ≤
            SupportFunction.supportFunction K.carrier
              (realLogCoordinate q.1) +
              ((n : ℝ) *
                LaurentJetSeparatedness.bodyRadius K) * 2
          at hsupport
        change
          MomentRegularity.momentNormalizedPotential
              F (realLogCoordinate (q.1 - y.1)) ≤
            SupportFunction.supportFunction K.carrier
              (realLogCoordinate (q.1 - y.1)) +
              Real.log
                (finiteEnergySourcePartition F /
                  normalizedVolume K.carrier)
          at hnormpot
        calc
          momentWeakJointCoverUpperEnvelope
              K F htransport p (q - y) ≤
            momentWeakJointCoverFiniteMajorant K F (q - y) :=
              momentWeakJointCoverUpperEnvelope_le_majorant
                K F htransport p (q - y)
          _ ≤ C := by
            dsimp [C,
              momentWeakHolomorphicJointMollifierSupportError,
              momentWeakJointCoverFiniteMajorant]
            linarith
    _ = C := by
      rw [MeasureTheory.integral_mul_const,
        integral_sourceJointTrueRadialMollifier, one_mul]

private def momentWeakHolomorphicJointTimeSupportError
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K) (t : ℝ) : ℝ :=
  Real.log
      (finiteEnergySourcePartition F /
        normalizedVolume K.carrier) +
    BodyScale.canonicalScale K + 1 +
    BodyScale.canonicalScale K *
      (|t| + ‖sourceJointRealTimeCLM n‖) +
    ((n : ℝ) * LaurentJetSeparatedness.bodyRadius K) * 2

private theorem momentWeakHolomorphicJointTimeMollification_le_support_add
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) (k : ℕ) (t : ℝ) :
    momentWeakHolomorphicJointTrueRadialMollification
      K F htransport p k (sourceJointTimeEmbedding z t) ≤
      SupportFunction.supportFunction K.carrier
        (realLogCoordinate z) +
      momentWeakHolomorphicJointTimeSupportError K F t := by
  have h := momentWeakHolomorphicJointMollification_le_support_add
    K F htransport p k (sourceJointTimeEmbedding z t)
  have hspace :
      realLogCoordinate (sourceJointTimeEmbedding z t).1 =
        realLogCoordinate z := rfl
  rw [hspace] at h
  simpa only [momentWeakHolomorphicJointTimeSupportError, ge_iff_le,
    momentWeakHolomorphicJointMollifierSupportError, sourceJointCoverTime_timeEmbedding] using h

private theorem momentWeakHolomorphicStrictJointTorusWeight_le_support_add
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (t : ℝ)
    {ε : ℝ} (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (q : LogTorus n) :
    momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p ε k t q ≤
      SupportFunction.supportFunction K.carrier q.1 +
      ((1 - ε) *
          momentWeakHolomorphicJointTimeSupportError K F t +
        ε * ((n : ℝ) * Real.log 2)) := by
  have hweak :=
    momentWeakHolomorphicJointTimeMollification_le_support_add
      K F htransport p (sourceTorusCoverPoint q) k t
  rw [realLogCoordinate_sourceTorusCoverPoint] at hweak
  have hstrict :=
    momentBodyStrictRadialPotential_le_support_add K q.1
  have hweak' := mul_le_mul_of_nonneg_left hweak
    (sub_nonneg.mpr hε₁)
  have hstrict' := mul_le_mul_of_nonneg_left hstrict hε₀
  rw [momentWeakHolomorphicStrictJointTorusWeight,
    jointSourceTorusWeight_eq_cover]
  unfold momentWeakHolomorphicStrictJointCoverWeight
  have href :
      MatrixTorusBochnerBridge.matrixSourceCoverPotential
        (momentBodyStrictRadialPotential K)
        (sourceJointTimeEmbedding (sourceTorusCoverPoint q) t).1 =
        momentBodyStrictRadialPotential K q.1 := by
    simp only [sourceJointTimeEmbedding, sourceTorusCoverPoint,
      MatrixTorusBochnerBridge.matrixSourceCoverPotential_logarithmicPoint]
  rw [href]
  nlinarith

private theorem momentWeakHolomorphicStrictJoint_centered_mem_resolventDefect_range_closure
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (t : ℝ)
    {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (f : angularWeightedScalarL2
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k t))
    (hf :
      (∫ q : LogTorus n,
        f q ∂(angularWeightedTorusMeasure
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t))) = 0) :
    f ∈
      ((ContinuousLinearMap.id ℂ
        (angularWeightedScalarL2
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t)) -
        angularWeakScalarResolventCLM
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t)).range).topologicalClosure := by
  let : IsFiniteMeasure
      (angularWeightedTorusMeasure
        (momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k t)) :=
    momentWeakHolomorphicStrictJointWeightedMeasure_isFinite
      K F htransport p k t hε₀ hε₁
  exact sourceFreeAngularCentered_mem_resolventDefect_range_closure
    K
    (continuous_momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p ε k t)
    (momentWeakHolomorphicStrictJointTorusWeight_le_support_add
      K F htransport p k t hε₀.le hε₁)
    f hf

end BergmanJetHolomorphicPhysicalSupport

namespace BergmanJetJointHolomorphicTimeDerivativeBounds

open Set Function Filter MeasureTheory Metric
open TorusCharacters WeightedTorusHilbert MatrixTorusBochnerBridge MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation BergmanJetEnvelopePlurisubharmonic
open BergmanJetUpperEnvelope BergmanJetStrictRadialRegularizer BergmanJetJointHolomorphicClosure
open BergmanJetJointHolomorphicPlurisubharmonicSmoothing BergmanJetJointHolomorphicStrictSchur
open ActualJetUpperEnvelope JetEnvelopeGlobalPlurisubharmonic JetEnvelopeRightDerivative
open JetEnvelopeTrueRadialMollifier EnvelopeSmoothing EnvelopeGeneralTorusDescent
open RadialAccelerationBounds
open scoped BigOperators ENNReal Topology ContDiff Convolution
  ComplexConjugate ComplexOrder

local instance sourceJointCoverVolume_isAddHaar (n : ℕ) :
    Measure.IsAddHaarMeasure
      (volume : Measure (SourceJointComplexCover n)) :=
  Measure.prod.instIsAddHaarMeasure
    (volume : Measure (LogSpace n)) (volume : Measure ℂ)

private theorem upperRegularization_sourceJointCover_translate_le
    {n : ℕ} (f : SourceJointComplexCover n → ℝ)
    (hlocal : ∀ q : SourceJointComplexCover n,
      (localUpperBounds f q).Nonempty)
    (d : SourceJointComplexCover n) (C : ℝ)
    (hshift : ∀ q : SourceJointComplexCover n,
      f (q + d) ≤ f q + C)
    (q : SourceJointComplexCover n) :
    upperRegularization f (q + d) ≤
      upperRegularization f q + C := by
  apply le_of_forall_pos_le_add
  intro η hη
  have happrox :
      ∃ c ∈ localUpperBounds f q,
        c < upperRegularization f q + η := by
    unfold upperRegularization
    exact exists_lt_of_csInf_lt (hlocal q)
      (lt_add_of_pos_right _ hη)
  obtain ⟨c, hc, hcη⟩ := happrox
  have hnear :
      ∀ᶠ y : SourceJointComplexCover n in 𝓝 q,
        f (y + d) ≤ c + C := by
    exact hc.mono fun y hy => by
      linarith [hshift y]
  have htranslate :
      ∀ᶠ y : SourceJointComplexCover n in 𝓝 (q + d),
        f y ≤ c + C := by
    have hevent :
        ∀ᶠ y : SourceJointComplexCover n in
          𝓝 ((Homeomorph.addRight d) q), f y ≤ c + C := by
      rw [← (Homeomorph.addRight d).map_nhds_eq q,
        Filter.eventually_map]
      simpa only [Homeomorph.addRight, Homeomorph.homeomorph_mk_coe, Equiv.coe_addRight,
        add_comm] using hnear
    simpa only [add_comm, Homeomorph.addRight, Homeomorph.homeomorph_mk_coe,
      Equiv.coe_addRight] using hevent
  have hreg := upperRegularization_le_of_eventually
    f (q + d) htranslate
  linarith

private theorem upperRegularization_sourceJointCover_le_translate
    {n : ℕ} (f : SourceJointComplexCover n → ℝ)
    (hlocal : ∀ q : SourceJointComplexCover n,
      (localUpperBounds f q).Nonempty)
    (d : SourceJointComplexCover n)
    (hshift : ∀ q : SourceJointComplexCover n,
      f q ≤ f (q + d))
    (q : SourceJointComplexCover n) :
    upperRegularization f q ≤
      upperRegularization f (q + d) := by
  apply le_of_forall_pos_le_add
  intro η hη
  have happrox :
      ∃ c ∈ localUpperBounds f (q + d),
        c < upperRegularization f (q + d) + η := by
    unfold upperRegularization
    exact exists_lt_of_csInf_lt (hlocal (q + d))
      (lt_add_of_pos_right _ hη)
  obtain ⟨c, hc, hcη⟩ := happrox
  change
    (∀ᶠ y : SourceJointComplexCover n in 𝓝 (q + d),
      f y ≤ c) at hc
  have htranslate :
      ∀ᶠ y : SourceJointComplexCover n in 𝓝 q,
        f (y + d) ≤ c := by
    have hevent :
        ∀ᶠ y : SourceJointComplexCover n in
          𝓝 ((Homeomorph.addRight d) q), f y ≤ c := by
      simpa only [Homeomorph.addRight, Homeomorph.homeomorph_mk_coe, Equiv.coe_addRight,
        add_comm] using hc
    rw [← (Homeomorph.addRight d).map_nhds_eq q,
      Filter.eventually_map] at hevent
    simpa only [add_comm, Homeomorph.addRight, Homeomorph.homeomorph_mk_coe,
      Equiv.coe_addRight] using hevent
  have hnear :
      ∀ᶠ y : SourceJointComplexCover n in 𝓝 q,
        f y ≤ c :=
    htranslate.mono fun y hy => (hshift y).trans hy
  have hreg := upperRegularization_le_of_eventually f q hnear
  linarith

private def momentWeakJointRealTimeShift (n : ℕ) (h : ℝ) :
    SourceJointComplexCover n :=
  ((0 : LogSpace n), (h / 2 : ℂ))

@[simp] private theorem sourceJointCoverTime_add_momentWeakJointRealTimeShift
    {n : ℕ} (q : SourceJointComplexCover n) (h : ℝ) :
    sourceJointCoverTime
      (q + momentWeakJointRealTimeShift n h) =
        sourceJointCoverTime q + h := by
  simp only [sourceJointCoverTime, momentWeakJointRealTimeShift, Prod.snd_add, Complex.add_re,
    Complex.div_ofNat_re, Complex.ofReal_re]
  ring

private theorem momentWeakJointCoverFiniteGeodesic_le_time_translate
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    {h : ℝ} (hh : 0 ≤ h) (q : SourceJointComplexCover n) :
    momentWeakJointCoverFiniteGeodesic
        K F htransport p k q ≤
      momentWeakJointCoverFiniteGeodesic
        K F htransport p k
          (q + momentWeakJointRealTimeShift n h) := by
  have htime :
      sourceJointCoverTime q ≤ sourceJointCoverTime q + h := by
    linarith
  have hmono := monotone_momentJetGeodesic
    K (Nat.zero_lt_succ k) F htransport p q.1
      (Nat.floor (BodyScale.canonicalScale K *
        ((k + 1 : ℕ) : ℝ))) htime
  unfold momentWeakJointCoverFiniteGeodesic
  rw [show
      (q + momentWeakJointRealTimeShift n h).1 = q.1 by
        simp only [momentWeakJointRealTimeShift, Prod.fst_add, add_zero],
    sourceJointCoverTime_add_momentWeakJointRealTimeShift]
  exact hmono

private theorem momentWeakJointCoverFiniteGeodesic_time_translate_le
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    {h : ℝ} (hh : 0 ≤ h) (q : SourceJointComplexCover n) :
    momentWeakJointCoverFiniteGeodesic
        K F htransport p k
          (q + momentWeakJointRealTimeShift n h) ≤
      momentWeakJointCoverFiniteGeodesic
        K F htransport p k q +
          BodyScale.canonicalScale K * h := by
  have htime :
      sourceJointCoverTime q ≤ sourceJointCoverTime q + h := by
    linarith
  have hshift := momentWeakBodyScaleJetGeodesic_time_shift_le
    K F htransport p q.1 k htime
  unfold momentWeakJointCoverFiniteGeodesic
  rw [show
      (q + momentWeakJointRealTimeShift n h).1 = q.1 by
        simp only [momentWeakJointRealTimeShift, Prod.fst_add, add_zero],
    sourceJointCoverTime_add_momentWeakJointRealTimeShift]
  simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, ge_iff_le,
    add_sub_cancel_left] using hshift

private theorem momentWeakJointCoverTailSup_le_time_translate
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ)
    {h : ℝ} (hh : 0 ≤ h) (q : SourceJointComplexCover n) :
    momentWeakJointCoverTailSup K F htransport p r q ≤
      momentWeakJointCoverTailSup K F htransport p r
        (q + momentWeakJointRealTimeShift n h) := by
  unfold momentWeakJointCoverTailSup
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨j, rfl⟩
  calc
    momentWeakJointCoverFiniteGeodesic
        K F htransport p
          (momentJointTailStart K F htransport p + r + j) q ≤
      momentWeakJointCoverFiniteGeodesic
        K F htransport p
          (momentJointTailStart K F htransport p + r + j)
          (q + momentWeakJointRealTimeShift n h) :=
      momentWeakJointCoverFiniteGeodesic_le_time_translate
        K F htransport p _ hh q
    _ ≤ sSup (Set.range fun i : ℕ =>
        momentWeakJointCoverFiniteGeodesic
          K F htransport p
            (momentJointTailStart K F htransport p + r + i)
            (q + momentWeakJointRealTimeShift n h)) := by
      apply le_csSup
        (momentWeakJointCoverTailSup_range_bddAbove
          K F htransport p r
            (q + momentWeakJointRealTimeShift n h))
      exact ⟨j, rfl⟩

private theorem momentWeakJointCoverTailSup_time_translate_le
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ)
    {h : ℝ} (hh : 0 ≤ h) (q : SourceJointComplexCover n) :
    momentWeakJointCoverTailSup K F htransport p r
        (q + momentWeakJointRealTimeShift n h) ≤
      momentWeakJointCoverTailSup K F htransport p r q +
        BodyScale.canonicalScale K * h := by
  unfold momentWeakJointCoverTailSup
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨j, rfl⟩
  calc
    momentWeakJointCoverFiniteGeodesic
        K F htransport p
          (momentJointTailStart K F htransport p + r + j)
          (q + momentWeakJointRealTimeShift n h) ≤
      momentWeakJointCoverFiniteGeodesic
        K F htransport p
          (momentJointTailStart K F htransport p + r + j) q +
            BodyScale.canonicalScale K * h :=
      momentWeakJointCoverFiniteGeodesic_time_translate_le
        K F htransport p _ hh q
    _ ≤ sSup (Set.range fun i : ℕ =>
        momentWeakJointCoverFiniteGeodesic
          K F htransport p
            (momentJointTailStart K F htransport p + r + i) q) +
          BodyScale.canonicalScale K * h := by
      apply add_le_add
      · apply le_csSup
          (momentWeakJointCoverTailSup_range_bddAbove
            K F htransport p r q)
        exact ⟨j, rfl⟩
      · exact le_rfl

private theorem momentWeakJointCoverTailUpperEnvelope_le_time_translate
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ)
    {h : ℝ} (hh : 0 ≤ h) (q : SourceJointComplexCover n) :
    momentWeakJointCoverTailUpperEnvelope
        K F htransport p r q ≤
      momentWeakJointCoverTailUpperEnvelope
        K F htransport p r
          (q + momentWeakJointRealTimeShift n h) := by
  unfold momentWeakJointCoverTailUpperEnvelope
  exact upperRegularization_sourceJointCover_le_translate
    (momentWeakJointCoverTailSup K F htransport p r)
    (momentWeakJointCoverTailSup_localUpperBounds_nonempty
      K F htransport p r)
    (momentWeakJointRealTimeShift n h)
    (momentWeakJointCoverTailSup_le_time_translate
      K F htransport p r hh) q

private theorem momentWeakJointCoverTailUpperEnvelope_time_translate_le
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ)
    {h : ℝ} (hh : 0 ≤ h) (q : SourceJointComplexCover n) :
    momentWeakJointCoverTailUpperEnvelope
        K F htransport p r
          (q + momentWeakJointRealTimeShift n h) ≤
      momentWeakJointCoverTailUpperEnvelope
        K F htransport p r q +
          BodyScale.canonicalScale K * h := by
  unfold momentWeakJointCoverTailUpperEnvelope
  exact upperRegularization_sourceJointCover_translate_le
    (momentWeakJointCoverTailSup K F htransport p r)
    (momentWeakJointCoverTailSup_localUpperBounds_nonempty
      K F htransport p r)
    (momentWeakJointRealTimeShift n h)
    (BodyScale.canonicalScale K * h)
    (momentWeakJointCoverTailSup_time_translate_le
      K F htransport p r hh) q

private theorem momentWeakJointCoverUpperEnvelope_le_time_translate
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n)
    {h : ℝ} (hh : 0 ≤ h) (q : SourceJointComplexCover n) :
    momentWeakJointCoverUpperEnvelope
        K F htransport p q ≤
      momentWeakJointCoverUpperEnvelope
        K F htransport p
          (q + momentWeakJointRealTimeShift n h) := by
  apply le_of_tendsto_of_tendsto
    (tendsto_momentWeakJointCoverTailUpperEnvelope
      K F htransport p q)
    (tendsto_momentWeakJointCoverTailUpperEnvelope
      K F htransport p
        (q + momentWeakJointRealTimeShift n h))
  exact Filter.Eventually.of_forall fun r =>
    momentWeakJointCoverTailUpperEnvelope_le_time_translate
      K F htransport p r hh q

private theorem momentWeakJointCoverUpperEnvelope_time_translate_le
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n)
    {h : ℝ} (hh : 0 ≤ h) (q : SourceJointComplexCover n) :
    momentWeakJointCoverUpperEnvelope
        K F htransport p
          (q + momentWeakJointRealTimeShift n h) ≤
      momentWeakJointCoverUpperEnvelope
        K F htransport p q +
          BodyScale.canonicalScale K * h := by
  have hright :
      Tendsto
        (fun r : ℕ =>
          momentWeakJointCoverTailUpperEnvelope
            K F htransport p r q +
              BodyScale.canonicalScale K * h)
        atTop
        (𝓝 (momentWeakJointCoverUpperEnvelope
          K F htransport p q +
            BodyScale.canonicalScale K * h)) :=
    (tendsto_momentWeakJointCoverTailUpperEnvelope
      K F htransport p q).add
        (tendsto_const_nhds :
          Tendsto
            (fun _ : ℕ => BodyScale.canonicalScale K * h)
            atTop
            (𝓝 (BodyScale.canonicalScale K * h)))
  apply le_of_tendsto_of_tendsto
    (tendsto_momentWeakJointCoverTailUpperEnvelope
      K F htransport p
        (q + momentWeakJointRealTimeShift n h))
    hright
  exact Filter.Eventually.of_forall fun r =>
    momentWeakJointCoverTailUpperEnvelope_time_translate_le
      K F htransport p r hh q

private theorem sourceJointTimeEmbedding_sub_eq_add_realTimeShift
    {n : ℕ} (z : LogSpace n)
    (y : SourceJointComplexCover n) (s t : ℝ) :
    sourceJointTimeEmbedding z t - y =
      (sourceJointTimeEmbedding z s - y) +
        momentWeakJointRealTimeShift n (t - s) := by
  apply Prod.ext
  · simp only [sourceJointTimeEmbedding, Prod.fst_sub, momentWeakJointRealTimeShift,
      Complex.ofReal_sub, Prod.fst_add, add_zero]
  · simp only [sourceJointTimeEmbedding, Prod.snd_sub, momentWeakJointRealTimeShift,
      Complex.ofReal_sub, Prod.snd_add]
    ring

private theorem abs_momentWeakJointCoverUpperEnvelope_timeEmbedding_sub_le
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) (y : SourceJointComplexCover n)
    (s t : ℝ) :
    |momentWeakJointCoverUpperEnvelope
        K F htransport p (sourceJointTimeEmbedding z t - y) -
      momentWeakJointCoverUpperEnvelope
        K F htransport p (sourceJointTimeEmbedding z s - y)| ≤
      BodyScale.canonicalScale K * |t - s| := by
  rcases le_total s t with hst | hts
  · have hh : 0 ≤ t - s := sub_nonneg.mpr hst
    have hident :=
      sourceJointTimeEmbedding_sub_eq_add_realTimeShift
        z y s t
    have hmono := momentWeakJointCoverUpperEnvelope_le_time_translate
      K F htransport p hh (sourceJointTimeEmbedding z s - y)
    have hupper :=
      momentWeakJointCoverUpperEnvelope_time_translate_le
        K F htransport p hh (sourceJointTimeEmbedding z s - y)
    rw [hident]
    rw [abs_of_nonneg (sub_nonneg.mpr hmono),
      abs_of_nonneg hh]
    linarith
  · have hh : 0 ≤ s - t := sub_nonneg.mpr hts
    have hident :=
      sourceJointTimeEmbedding_sub_eq_add_realTimeShift
        z y t s
    have hmono := momentWeakJointCoverUpperEnvelope_le_time_translate
      K F htransport p hh (sourceJointTimeEmbedding z t - y)
    have hupper :=
      momentWeakJointCoverUpperEnvelope_time_translate_le
        K F htransport p hh (sourceJointTimeEmbedding z t - y)
    rw [hident]
    rw [abs_of_nonpos (sub_nonpos.mpr hmono),
      abs_of_nonpos (sub_nonpos.mpr hts)]
    linarith

private theorem abs_momentWeakHolomorphicJointTrueRadialMollification_time_sub_le
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) (k : ℕ) (s t : ℝ) :
    |momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k (sourceJointTimeEmbedding z t) -
      momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k (sourceJointTimeEmbedding z s)| ≤
      BodyScale.canonicalScale K * |t - s| := by
  let ρ : SourceJointComplexCover n → ℝ :=
    sourceJointTrueRadialMollifier n k
  let E : SourceJointComplexCover n → ℝ :=
    momentWeakJointCoverUpperEnvelope K F htransport p
  let B : ℝ := BodyScale.canonicalScale K * |t - s|
  have hρ : Integrable ρ
      (volume : Measure (SourceJointComplexCover n)) :=
    integrable_sourceJointTrueRadialMollifier n k
  have ht : Integrable
      (fun y : SourceJointComplexCover n =>
        ρ y * E (sourceJointTimeEmbedding z t - y))
      (volume : Measure (SourceJointComplexCover n)) :=
    integrable_sourceJointTrueRadialMollifier_mul_translate
      (locallyIntegrable_momentWeakJointCoverUpperEnvelope
        K F htransport p)
      k (sourceJointTimeEmbedding z t)
  have hs : Integrable
      (fun y : SourceJointComplexCover n =>
        ρ y * E (sourceJointTimeEmbedding z s - y))
      (volume : Measure (SourceJointComplexCover n)) :=
    integrable_sourceJointTrueRadialMollifier_mul_translate
      (locallyIntegrable_momentWeakJointCoverUpperEnvelope
        K F htransport p)
      k (sourceJointTimeEmbedding z s)
  have hd : Integrable
      (fun y : SourceJointComplexCover n =>
        ρ y * E (sourceJointTimeEmbedding z t - y) -
          ρ y * E (sourceJointTimeEmbedding z s - y))
      (volume : Measure (SourceJointComplexCover n)) := ht.sub hs
  have hB : Integrable
      (fun y : SourceJointComplexCover n => ρ y * B)
      (volume : Measure (SourceJointComplexCover n)) :=
    hρ.mul_const B
  have hpoint (y : SourceJointComplexCover n) :
      ‖ρ y * E (sourceJointTimeEmbedding z t - y) -
        ρ y * E (sourceJointTimeEmbedding z s - y)‖ ≤
          ρ y * B := by
    have hnonneg : 0 ≤ ρ y :=
      sourceJointTrueRadialMollifier_nonneg n k y
    calc
      ‖ρ y * E (sourceJointTimeEmbedding z t - y) -
        ρ y * E (sourceJointTimeEmbedding z s - y)‖ =
        ρ y *
          |E (sourceJointTimeEmbedding z t - y) -
            E (sourceJointTimeEmbedding z s - y)| := by
          rw [← mul_sub, Real.norm_eq_abs, abs_mul,
            abs_of_nonneg hnonneg]
      _ ≤ ρ y * B := by
        apply mul_le_mul_of_nonneg_left _ hnonneg
        exact
          abs_momentWeakJointCoverUpperEnvelope_timeEmbedding_sub_le
            K F htransport p z y s t
  change
    |sourceJointTrueRadialSmoothed E k
        (sourceJointTimeEmbedding z t) -
      sourceJointTrueRadialSmoothed E k
        (sourceJointTimeEmbedding z s)| ≤ B
  unfold sourceJointTrueRadialSmoothed
  rw [MeasureTheory.convolution_def,
    MeasureTheory.convolution_def]
  change
    |(∫ y : SourceJointComplexCover n,
        ρ y * E (sourceJointTimeEmbedding z t - y)) -
      (∫ y : SourceJointComplexCover n,
        ρ y * E (sourceJointTimeEmbedding z s - y))| ≤ B
  rw [← MeasureTheory.integral_sub ht hs, ← Real.norm_eq_abs]
  calc
    ‖∫ y : SourceJointComplexCover n,
        (ρ y * E (sourceJointTimeEmbedding z t - y) -
          ρ y * E (sourceJointTimeEmbedding z s - y))‖ ≤
      ∫ y : SourceJointComplexCover n,
        ‖ρ y * E (sourceJointTimeEmbedding z t - y) -
          ρ y * E (sourceJointTimeEmbedding z s - y)‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ y : SourceJointComplexCover n, ρ y * B :=
      MeasureTheory.integral_mono hd.norm hB hpoint
    _ = B := by
      rw [MeasureTheory.integral_mul_const]
      change
        (∫ y : SourceJointComplexCover n,
          sourceJointTrueRadialMollifier n k y) * B = B
      rw [integral_sourceJointTrueRadialMollifier, one_mul]

private theorem abs_momentWeakHolomorphicStrictJointTorusWeight_time_sub_le
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (s t : ℝ) (q : LogTorus n) :
    |momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k t q -
      momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k s q| ≤
      BodyScale.canonicalScale K * |t - s| := by
  have hc₀ : 0 ≤ 1 - ε := sub_nonneg.mpr hε₁
  have hc₁ : 1 - ε ≤ 1 := sub_le_self 1 hε₀
  have hB : 0 ≤ BodyScale.canonicalScale K * |t - s| :=
    mul_nonneg (BodyScale.canonicalScale_pos K).le
      (abs_nonneg _)
  rw [momentWeakHolomorphicStrictJointTorusWeight,
    jointSourceTorusWeight_eq_cover,
    momentWeakHolomorphicStrictJointTorusWeight,
    jointSourceTorusWeight_eq_cover]
  unfold momentWeakHolomorphicStrictJointCoverWeight
  simp only [sourceJointTimeEmbedding]
  calc
    |((1 - ε) *
          momentWeakHolomorphicJointTrueRadialMollification
            K F htransport p k
              (sourceTorusCoverPoint q, (t / 2 : ℂ)) +
          ε * matrixSourceCoverPotential
            (momentBodyStrictRadialPotential K)
              (sourceTorusCoverPoint q)) -
        ((1 - ε) *
          momentWeakHolomorphicJointTrueRadialMollification
            K F htransport p k
              (sourceTorusCoverPoint q, (s / 2 : ℂ)) +
          ε * matrixSourceCoverPotential
            (momentBodyStrictRadialPotential K)
              (sourceTorusCoverPoint q))| =
      (1 - ε) *
        |momentWeakHolomorphicJointTrueRadialMollification
            K F htransport p k
              (sourceJointTimeEmbedding
                (sourceTorusCoverPoint q) t) -
          momentWeakHolomorphicJointTrueRadialMollification
            K F htransport p k
              (sourceJointTimeEmbedding
                (sourceTorusCoverPoint q) s)| := by
      simp only [sourceJointTimeEmbedding]
      calc
        _ = |(1 - ε) *
          (momentWeakHolomorphicJointTrueRadialMollification
            K F htransport p k
              (sourceTorusCoverPoint q, (t / 2 : ℂ)) -
            momentWeakHolomorphicJointTrueRadialMollification
              K F htransport p k
                (sourceTorusCoverPoint q, (s / 2 : ℂ)))| := by
          congr 1
          ring
        _ = _ := by
          rw [abs_mul, abs_of_nonneg hc₀]
    _ ≤ (1 - ε) *
          (BodyScale.canonicalScale K * |t - s|) :=
      mul_le_mul_of_nonneg_left
        (abs_momentWeakHolomorphicJointTrueRadialMollification_time_sub_le
          K F htransport p (sourceTorusCoverPoint q) k s t)
        hc₀
    _ ≤ BodyScale.canonicalScale K * |t - s| := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc₁ hB

private theorem abs_momentWeakHolomorphicStrictJointTorusVelocity_le
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (t : ℝ) (q : LogTorus n) :
    |jointSourceTorusVelocity
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k) t q| ≤
      BodyScale.canonicalScale K := by
  have hG : ContDiff ℝ 2
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k) :=
    (contDiff_infty.mp
      (contDiff_momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)) 2
  have hderiv := hasDerivAt_jointSourceTorusWeight hG t q
  have hlip :
      ∀ᶠ u : ℝ in 𝓝 t,
        ‖jointSourceTorusWeight
              (momentWeakHolomorphicStrictJointCoverWeight
                K F htransport p ε k) u q -
            jointSourceTorusWeight
              (momentWeakHolomorphicStrictJointCoverWeight
                K F htransport p ε k) t q‖ ≤
          BodyScale.canonicalScale K * ‖u - t‖ := by
    exact Filter.Eventually.of_forall fun u => by
      simpa only [Real.norm_eq_abs, momentWeakHolomorphicStrictJointTorusWeight] using
          abs_momentWeakHolomorphicStrictJointTorusWeight_time_sub_le
            K F htransport p ε hε₀ hε₁ k t u q
  simpa only [ge_iff_le, Real.norm_eq_abs] using
    hderiv.le_of_lip' (BodyScale.canonicalScale_pos K).le
      hlip

private theorem abs_jointSourceCoverVelocity_momentWeakHolomorphicJointMollification_time_sub_le
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) (k : ℕ) (s t : ℝ) :
    |jointSourceCoverVelocity
        (momentWeakHolomorphicJointTrueRadialMollification
          K F htransport p k)
          (sourceJointTimeEmbedding z t) -
      jointSourceCoverVelocity
        (momentWeakHolomorphicJointTrueRadialMollification
          K F htransport p k)
          (sourceJointTimeEmbedding z s)| ≤
      BodyScale.canonicalScale K *
        sourceJointTrueRadialTimeKernelMass n k * |t - s| := by
  let ρ : SourceJointComplexCover n → ℝ :=
    sourceJointTrueRadialTimeKernel n k
  let E : SourceJointComplexCover n → ℝ :=
    momentWeakJointCoverUpperEnvelope K F htransport p
  let B : ℝ := BodyScale.canonicalScale K * |t - s|
  have hE : LocallyIntegrable E
      (volume : Measure (SourceJointComplexCover n)) :=
    locallyIntegrable_momentWeakJointCoverUpperEnvelope
      K F htransport p
  have hρ : Integrable ρ
      (volume : Measure (SourceJointComplexCover n)) :=
    integrable_sourceJointTrueRadialTimeKernel n k
  have ht : Integrable
      (fun y : SourceJointComplexCover n =>
        ρ y * E (sourceJointTimeEmbedding z t - y))
      (volume : Measure (SourceJointComplexCover n)) := by
    have hconv :=
      (hasCompactSupport_sourceJointTrueRadialTimeKernel n k).convolutionExists_left
        (ContinuousLinearMap.lsmul ℝ ℝ)
        (continuous_sourceJointTrueRadialTimeKernel n k)
        hE (sourceJointTimeEmbedding z t)
    refine hconv.integrable.congr
      (Filter.Eventually.of_forall fun y => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, E, ρ]
  have hs : Integrable
      (fun y : SourceJointComplexCover n =>
        ρ y * E (sourceJointTimeEmbedding z s - y))
      (volume : Measure (SourceJointComplexCover n)) := by
    have hconv :=
      (hasCompactSupport_sourceJointTrueRadialTimeKernel n k).convolutionExists_left
        (ContinuousLinearMap.lsmul ℝ ℝ)
        (continuous_sourceJointTrueRadialTimeKernel n k)
        hE (sourceJointTimeEmbedding z s)
    refine hconv.integrable.congr
      (Filter.Eventually.of_forall fun y => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, E, ρ]
  have hd : Integrable
      (fun y : SourceJointComplexCover n =>
        ρ y * E (sourceJointTimeEmbedding z t - y) -
          ρ y * E (sourceJointTimeEmbedding z s - y))
      (volume : Measure (SourceJointComplexCover n)) := ht.sub hs
  have hmajor : Integrable
      (fun y : SourceJointComplexCover n => |ρ y| * B)
      (volume : Measure (SourceJointComplexCover n)) := by
    simpa only [Real.norm_eq_abs] using hρ.norm.mul_const B
  have hpoint (y : SourceJointComplexCover n) :
      ‖ρ y * E (sourceJointTimeEmbedding z t - y) -
        ρ y * E (sourceJointTimeEmbedding z s - y)‖ ≤
          |ρ y| * B := by
    rw [← mul_sub, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (abs_momentWeakJointCoverUpperEnvelope_timeEmbedding_sub_le
        K F htransport p z y s t)
      (abs_nonneg _)
  rw [show
    jointSourceCoverVelocity
      (momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k)
      (sourceJointTimeEmbedding z t) =
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        (volume : Measure (SourceJointComplexCover n))] E)
        (sourceJointTimeEmbedding z t) from
          jointSourceCoverVelocity_sourceJointTrueRadialSmoothed
            hE k (sourceJointTimeEmbedding z t),
    show
    jointSourceCoverVelocity
      (momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k)
      (sourceJointTimeEmbedding z s) =
      (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        (volume : Measure (SourceJointComplexCover n))] E)
        (sourceJointTimeEmbedding z s) from
          jointSourceCoverVelocity_sourceJointTrueRadialSmoothed
            hE k (sourceJointTimeEmbedding z s)]
  rw [MeasureTheory.convolution_def,
    MeasureTheory.convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [← integral_sub ht hs, ← Real.norm_eq_abs]
  calc
    ‖∫ y : SourceJointComplexCover n,
        (ρ y * E (sourceJointTimeEmbedding z t - y) -
          ρ y * E (sourceJointTimeEmbedding z s - y))‖ ≤
      ∫ y : SourceJointComplexCover n,
        ‖ρ y * E (sourceJointTimeEmbedding z t - y) -
          ρ y * E (sourceJointTimeEmbedding z s - y)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y : SourceJointComplexCover n, |ρ y| * B :=
      integral_mono hd.norm hmajor hpoint
    _ = sourceJointTrueRadialTimeKernelMass n k * B := by
      rw [integral_mul_const]
      rfl
    _ = BodyScale.canonicalScale K *
        sourceJointTrueRadialTimeKernelMass n k * |t - s| := by
      dsimp [B]
      ring

private theorem momentWeakHolomorphicStrictJointTorusVelocity_eq_mollified
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ)
    (q : LogTorus n) :
    jointSourceTorusVelocity
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t q =
      (1 - ε) *
        jointSourceTorusVelocity
          (momentWeakHolomorphicJointTrueRadialMollification
            K F htransport p k) t q := by
  let M : SourceJointComplexCover n → ℝ :=
    momentWeakHolomorphicJointTrueRadialMollification
      K F htransport p k
  let G : SourceJointComplexCover n → ℝ :=
    momentWeakHolomorphicStrictJointCoverWeight
      K F htransport p ε k
  have hM : ContDiff ℝ 2 M := by
    dsimp [M]
    exact (contDiff_infty.mp
      (contDiff_momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k)) 2
  have hG : ContDiff ℝ 2 G := by
    dsimp [G]
    exact (contDiff_infty.mp
      (contDiff_momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)) 2
  have hraw := hasDerivAt_jointSourceTorusWeight hM t q
  have hscaled : HasDerivAt
      (fun u : ℝ =>
        (1 - ε) * jointSourceTorusWeight M u q +
          ε * matrixSourceCoverPotential
            (momentBodyStrictRadialPotential K)
              (sourceTorusCoverPoint q))
      ((1 - ε) * jointSourceTorusVelocity M t q) t :=
    (hraw.const_mul (1 - ε)).add_const
      (ε * matrixSourceCoverPotential
        (momentBodyStrictRadialPotential K)
          (sourceTorusCoverPoint q))
  have heq :
      (fun u : ℝ => jointSourceTorusWeight G u q) =
      (fun u : ℝ =>
        (1 - ε) * jointSourceTorusWeight M u q +
          ε * matrixSourceCoverPotential
            (momentBodyStrictRadialPotential K)
              (sourceTorusCoverPoint q)) := by
    funext u
    rw [jointSourceTorusWeight_eq_cover,
      jointSourceTorusWeight_eq_cover]
    rfl
  have hderived : HasDerivAt
      (fun u : ℝ => jointSourceTorusWeight G u q)
      ((1 - ε) * jointSourceTorusVelocity M t q) t := by
    rw [heq]
    exact hscaled
  have huniq :=
    (hasDerivAt_jointSourceTorusWeight hG t q).unique hderived
  exact huniq

private theorem abs_momentWeakHolomorphicStrictJointTorusVelocity_time_sub_le
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (s t : ℝ) (q : LogTorus n) :
    |jointSourceTorusVelocity
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t q -
      jointSourceTorusVelocity
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) s q| ≤
      BodyScale.canonicalScale K *
        sourceJointTrueRadialTimeKernelMass n k * |t - s| := by
  have hc₀ : 0 ≤ 1 - ε := sub_nonneg.mpr hε₁
  have hc₁ : 1 - ε ≤ 1 := sub_le_self 1 hε₀
  have hB : 0 ≤
      BodyScale.canonicalScale K *
        sourceJointTrueRadialTimeKernelMass n k * |t - s| :=
    mul_nonneg
      (mul_nonneg (BodyScale.canonicalScale_pos K).le
        (sourceJointTrueRadialTimeKernelMass_nonneg n k))
      (abs_nonneg _)
  rw [momentWeakHolomorphicStrictJointTorusVelocity_eq_mollified
      K F htransport p ε k t q,
    momentWeakHolomorphicStrictJointTorusVelocity_eq_mollified
      K F htransport p ε k s q,
    ← mul_sub, abs_mul, abs_of_nonneg hc₀]
  calc
    (1 - ε) *
        |jointSourceTorusVelocity
            (momentWeakHolomorphicJointTrueRadialMollification
              K F htransport p k) t q -
          jointSourceTorusVelocity
            (momentWeakHolomorphicJointTrueRadialMollification
              K F htransport p k) s q| ≤
      (1 - ε) *
        (BodyScale.canonicalScale K *
          sourceJointTrueRadialTimeKernelMass n k * |t - s|) := by
        apply mul_le_mul_of_nonneg_left _ hc₀
        rw [jointSourceTorusVelocity_eq_cover,
          jointSourceTorusVelocity_eq_cover]
        exact
          abs_jointSourceCoverVelocity_momentWeakHolomorphicJointMollification_time_sub_le
            K F htransport p (sourceTorusCoverPoint q) k s t
    _ ≤ BodyScale.canonicalScale K *
          sourceJointTrueRadialTimeKernelMass n k * |t - s| := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc₁ hB

private theorem abs_momentWeakHolomorphicStrictJointTorusAcceleration_le
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (t : ℝ) (q : LogTorus n) :
    |jointSourceTorusAcceleration
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t q| ≤
      BodyScale.canonicalScale K *
        sourceJointTrueRadialTimeKernelMass n k := by
  let G : SourceJointComplexCover n → ℝ :=
    momentWeakHolomorphicStrictJointCoverWeight
      K F htransport p ε k
  have hG : ContDiff ℝ 2 G := by
    dsimp [G]
    exact (contDiff_infty.mp
      (contDiff_momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)) 2
  have hB : 0 ≤
      BodyScale.canonicalScale K *
        sourceJointTrueRadialTimeKernelMass n k :=
    mul_nonneg (BodyScale.canonicalScale_pos K).le
      (sourceJointTrueRadialTimeKernelMass_nonneg n k)
  have hderiv := hasDerivAt_jointSourceTorusVelocity hG t q
  have hlip :
      ∀ᶠ u : ℝ in 𝓝 t,
        ‖jointSourceTorusVelocity G u q -
            jointSourceTorusVelocity G t q‖ ≤
          (BodyScale.canonicalScale K *
            sourceJointTrueRadialTimeKernelMass n k) * ‖u - t‖ := by
    exact Filter.Eventually.of_forall fun u => by
      simpa only [Real.norm_eq_abs, G] using
        abs_momentWeakHolomorphicStrictJointTorusVelocity_time_sub_le
          K F htransport p ε hε₀ hε₁ k t u q
  simpa only [ge_iff_le, Real.norm_eq_abs] using
    hderiv.le_of_lip' hB hlip

private theorem exists_momentWeakHolomorphicStrictJointTorusVelocity_local_bound
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (t : ℝ) :
    ∃ B : ℝ, ∀ u ∈ Metric.ball t (t / 2),
      ∀ q : LogTorus n,
        |jointSourceTorusVelocity
          (momentWeakHolomorphicStrictJointCoverWeight
            K F htransport p ε k) u q| ≤ B := by
  refine ⟨BodyScale.canonicalScale K, ?_⟩
  intro u _ q
  exact abs_momentWeakHolomorphicStrictJointTorusVelocity_le
    K F htransport p ε hε₀ hε₁ k u q

private theorem exists_momentWeakHolomorphicStrictJointTorusAcceleration_local_bound
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (t : ℝ) :
    ∃ J : ℝ, ∀ u ∈ Metric.ball t (t / 2),
      ∀ q : LogTorus n,
        |jointSourceTorusAcceleration
          (momentWeakHolomorphicStrictJointCoverWeight
            K F htransport p ε k) u q| ≤ J := by
  refine ⟨BodyScale.canonicalScale K *
    sourceJointTrueRadialTimeKernelMass n k, ?_⟩
  intro u _ q
  exact abs_momentWeakHolomorphicStrictJointTorusAcceleration_le
    K F htransport p ε hε₀ hε₁ k u q

end BergmanJetJointHolomorphicTimeDerivativeBounds

namespace BergmanJetHolomorphicPhysicalLogConvexity

open Set Function Filter MeasureTheory Metric Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeRightDerivative LogPartitionConvexity
open JointHolomorphicLaurentFourierCompatibility EnvelopeSmoothing EnvelopeGeneralTorusDescent
open EqualitySaturatingKillingPaths ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity
open MatrixTorusBochnerIdentity MatrixTorusBochnerCoreApproximation WeightedTorusDolbeault
open WeightedTorusBrascampLieb MatrixTorusDolbeaultGraph RadialSchurBlock TorusDeckGraphAdjoint
open RadialPhysicalInverseSquareRootEnergy MomentOptimizer MomentTargetGeodesic MomentFirstVariation
open BergmanJetJointHolomorphicStrictSchur BergmanJetJointHolomorphicFullLeviSchur
open BergmanJetHolomorphicPhysicalMeasure BergmanJetHolomorphicPhysicalSupport
open BergmanJetJointHolomorphicPhysicalApproximation BergmanJetJointHolomorphicTimeDerivativeBounds
open TorusHomogeneousBrascampLieb
open scoped BigOperators ENNReal ComplexConjugate ComplexOrder
  MatrixOrder InnerProductSpace Topology ContDiff

private theorem sourceFreeTimeDensity_integrable_of_majorant
    {n : ℕ}
    (a : ℝ → LogTorus n → ℝ) (t : ℝ)
    (ha : Continuous (a t))
    (M : LogTorus n → ℝ)
    (hM : Integrable M (sourceTorusBaseMeasure n))
    (hdom : ∀ q : LogTorus n, sourceTimeDensity a t q ≤ M q) :
    Integrable (sourceTimeDensity a t) (sourceTorusBaseMeasure n) := by
  apply hM.mono'
    ((Real.continuous_exp.comp ha.neg).aestronglyMeasurable)
  filter_upwards [] with q
  change |Real.exp (-a t q)| ≤ M q
  rw [abs_of_pos (Real.exp_pos _)]
  exact hdom q

private theorem sourceFreeWeightedObservable_integrable_of_majorant
    {n : ℕ}
    (a : ℝ → LogTorus n → ℝ)
    (F : LogTorus n → ℝ) (t B : ℝ)
    (ha : Continuous (a t)) (hF : Continuous F)
    (M : LogTorus n → ℝ)
    (hM : Integrable M (sourceTorusBaseMeasure n))
    (hdom : ∀ q : LogTorus n, sourceTimeDensity a t q ≤ M q)
    (hbound : ∀ q : LogTorus n, |F q| ≤ B) :
    Integrable (fun q => F q * sourceTimeDensity a t q)
      (sourceTorusBaseMeasure n) := by
  have hmajor := hM.norm.const_mul |B|
  apply hmajor.mono'
    ((hF.mul (Real.continuous_exp.comp ha.neg)).aestronglyMeasurable)
  filter_upwards [] with q
  change |F q * Real.exp (-a t q)| ≤
    |B| * ‖M q‖
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have hnonneg : 0 ≤ M q :=
    (Real.exp_pos (-a t q)).le.trans (hdom q)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  calc
    |F q| * Real.exp (-a t q) ≤ |B| * M q :=
      mul_le_mul
        ((hbound q).trans (le_abs_self B))
        (hdom q) (Real.exp_pos _).le (abs_nonneg _)
    _ = |B| * M q := rfl

private theorem sourceFree_integral_sourceProbability_eq_density_integral
    {n : ℕ}
    (a : ℝ → LogTorus n → ℝ) (t : ℝ)
    (ha : Continuous (a t))
    (hpart : 0 < sourcePartition a t)
    (F : LogTorus n → ℝ) :
    (∫ q : LogTorus n, F q ∂(sourceProbability a t)) =
      ∫ q : LogTorus n,
        F q * sourceNormalizedDensity a t q
          ∂(sourceTorusBaseMeasure n) := by
  have hcontinuous : Continuous (sourceNormalizedDensity a t) :=
    (Real.continuous_exp.comp ha.neg).div_const _
  have hmeas : Measurable
      (fun q : LogTorus n =>
        ENNReal.ofReal (sourceNormalizedDensity a t q)) :=
    ENNReal.measurable_ofReal.comp hcontinuous.measurable
  have hfinite :
      ∀ᵐ q ∂(sourceTorusBaseMeasure n),
        ENNReal.ofReal (sourceNormalizedDensity a t q) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [sourceProbability,
    integral_withDensity_eq_integral_toReal_smul hmeas hfinite]
  apply integral_congr_ae
  filter_upwards [] with q
  have hpos : 0 ≤ sourceNormalizedDensity a t q :=
    (div_pos (Real.exp_pos _) hpart).le
  rw [ENNReal.toReal_ofReal hpos]
  simp only [smul_eq_mul, mul_comm]

private theorem sourceFreeProbabilityMean_velocity_eq_logSlope
    {n : ℕ}
    (a f : ℝ → LogTorus n → ℝ) (t : ℝ)
    (ha : Continuous (a t))
    (hpart : 0 < sourcePartition a t) :
    sourceProbabilityMean a t (f t) = sourceLogSlope a f t := by
  unfold sourceProbabilityMean sourceLogSlope
  rw [sourceFree_integral_sourceProbability_eq_density_integral
    a t ha hpart (f t)]
  calc
    (∫ q : LogTorus n,
      f t q * sourceNormalizedDensity a t q
        ∂(sourceTorusBaseMeasure n)) =
      ∫ q : LogTorus n,
        (f t q * sourceTimeDensity a t q) /
          sourcePartition a t ∂(sourceTorusBaseMeasure n) := by
            apply integral_congr_ae
            filter_upwards [] with q
            simp only [sourceNormalizedDensity, mul_div_assoc]
    _ = sourceFirstMoment a f t / sourcePartition a t := by
      rw [integral_div]
      rfl

private theorem sourceFree_integral_sourceProbability_velocity_sq_eq_secondMoment
    {n : ℕ}
    (a f : ℝ → LogTorus n → ℝ) (t : ℝ)
    (ha : Continuous (a t))
    (hpart : 0 < sourcePartition a t) :
    (∫ q : LogTorus n,
      f t q ^ 2 ∂(sourceProbability a t)) =
      sourceSecondMoment a f t / sourcePartition a t := by
  rw [sourceFree_integral_sourceProbability_eq_density_integral
    a t ha hpart (fun q => f t q ^ 2)]
  calc
    (∫ q : LogTorus n,
      f t q ^ 2 * sourceNormalizedDensity a t q
        ∂(sourceTorusBaseMeasure n)) =
      ∫ q : LogTorus n,
        (f t q ^ 2 * sourceTimeDensity a t q) /
          sourcePartition a t ∂(sourceTorusBaseMeasure n) := by
            apply integral_congr_ae
            filter_upwards [] with q
            simp only [sourceNormalizedDensity, mul_div_assoc]
    _ = sourceSecondMoment a f t / sourcePartition a t := by
      rw [integral_div]
      rfl

private theorem sourceFreeProbabilityMean_acceleration_eq_moment
    {n : ℕ}
    (a j : ℝ → LogTorus n → ℝ) (t : ℝ)
    (ha : Continuous (a t))
    (hpart : 0 < sourcePartition a t) :
    sourceProbabilityMean a t (j t) =
      sourceAccelerationMoment a j t / sourcePartition a t := by
  unfold sourceProbabilityMean
  rw [sourceFree_integral_sourceProbability_eq_density_integral
    a t ha hpart (j t)]
  calc
    (∫ q : LogTorus n,
      j t q * sourceNormalizedDensity a t q
        ∂(sourceTorusBaseMeasure n)) =
      ∫ q : LogTorus n,
        (j t q * sourceTimeDensity a t q) /
          sourcePartition a t ∂(sourceTorusBaseMeasure n) := by
            apply integral_congr_ae
            filter_upwards [] with q
            simp only [sourceNormalizedDensity, mul_div_assoc]
    _ = sourceAccelerationMoment a j t / sourcePartition a t := by
      rw [integral_div]
      rfl

private theorem sourceFreeProbability_memLp_two_of_bound
    {n : ℕ}
    (a : ℝ → LogTorus n → ℝ)
    (F : LogTorus n → ℝ) (t B : ℝ)
    (hprob : IsProbabilityMeasure (sourceProbability a t))
    (hF : Continuous F)
    (hbound : ∀ q : LogTorus n, |F q| ≤ B) :
    MemLp F 2 (sourceProbability a t) := by
  let : IsProbabilityMeasure (sourceProbability a t) := hprob
  apply MemLp.of_bound hF.aestronglyMeasurable |B|
  filter_upwards [] with q
  simpa only [Real.norm_eq_abs] using
    (hbound q).trans (le_abs_self B)

private theorem sourceFreeProbabilityVariance_eq_momentVariance
    {n : ℕ}
    (a f : ℝ → LogTorus n → ℝ) (t : ℝ)
    (ha : Continuous (a t)) (hf : Continuous (f t))
    (hpart : 0 < sourcePartition a t)
    (hprob : IsProbabilityMeasure (sourceProbability a t))
    (hmem : MemLp (f t) 2 (sourceProbability a t)) :
    sourceProbabilityVariance a t (f t) =
      sourceMomentVariance a f t := by
  let : IsProbabilityMeasure (sourceProbability a t) := hprob
  have hvariance := ProbabilityTheory.variance_eq_sub hmem
  rw [ProbabilityTheory.variance_eq_integral
    hf.measurable.aemeasurable] at hvariance
  have hreal :
      sourceProbabilityVariance a t (f t) =
        (∫ q : LogTorus n,
          f t q ^ 2 ∂(sourceProbability a t)) -
          (sourceProbabilityMean a t (f t)) ^ 2 := by
    simpa only [sourceProbabilityVariance, sourceProbabilityMean, Pi.pow_apply] using hvariance
  rw [sourceFree_integral_sourceProbability_velocity_sq_eq_secondMoment
    a f t ha hpart,
    sourceFreeProbabilityMean_velocity_eq_logSlope
      a f t ha hpart] at hreal
  exact hreal

private theorem hasDerivAt_sourceFreePartition_of_majorant
    {n : ℕ}
    (a f : ℝ → LogTorus n → ℝ)
    {t : ℝ} {s : Set ℝ} {B : ℝ}
    (hs : s ∈ 𝓝 t)
    (ha : ∀ u : ℝ, Continuous (a u))
    (hf : ∀ u : ℝ, Continuous (f u))
    (hderiv : ∀ (u : ℝ) (q : LogTorus n),
      HasDerivAt (fun v : ℝ => a v q) (f u q) u)
    (M : LogTorus n → ℝ)
    (hM : Integrable M (sourceTorusBaseMeasure n))
    (hdom : ∀ u ∈ s, ∀ q : LogTorus n,
      sourceTimeDensity a u q ≤ M q)
    (hbound : ∀ u ∈ s, ∀ q : LogTorus n, |f u q| ≤ B) :
    HasDerivAt (sourcePartition a)
      (-sourceFirstMoment a f t) t := by
  have ht : t ∈ s := mem_of_mem_nhds hs
  have hmajor :
      Integrable (fun q : LogTorus n => |B| * ‖M q‖)
        (sourceTorusBaseMeasure n) := by
    exact hM.norm.const_mul |B|
  have hmeas :
      ∀ᶠ u in 𝓝 t,
        AEStronglyMeasurable
          (sourceTimeDensity a u) (sourceTorusBaseMeasure n) :=
    Filter.Eventually.of_forall fun u =>
      (Real.continuous_exp.comp (ha u).neg).aestronglyMeasurable
  have hdiffmeas : AEStronglyMeasurable
      (fun q : LogTorus n =>
        -f t q * sourceTimeDensity a t q)
      (sourceTorusBaseMeasure n) :=
    ((hf t).neg.mul
      (Real.continuous_exp.comp (ha t).neg)).aestronglyMeasurable
  have hdom' :
      ∀ᵐ q ∂(sourceTorusBaseMeasure n),
        ∀ u ∈ s,
          ‖-f u q * sourceTimeDensity a u q‖ ≤
            |B| * ‖M q‖ := by
    filter_upwards [] with q u hu
    change |-f u q * Real.exp (-a u q)| ≤ |B| * ‖M q‖
    rw [abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul
      ((hbound u hu q).trans (le_abs_self B))
      ((hdom u hu q).trans (le_abs_self _))
      (Real.exp_pos _).le (abs_nonneg _)
  have hdiff :
      ∀ᵐ q ∂(sourceTorusBaseMeasure n),
        ∀ u ∈ s,
          HasDerivAt
            (fun v : ℝ => sourceTimeDensity a v q)
            (-f u q * sourceTimeDensity a u q) u := by
    filter_upwards [] with q u _
    simpa only [sourceTimeDensity, neg_mul, Pi.neg_apply, mul_comm] using
      (hderiv u q).neg.exp
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := sourceTorusBaseMeasure n)
    (F := fun u q => sourceTimeDensity a u q)
    (F' := fun u q => -f u q * sourceTimeDensity a u q)
    (bound := fun q => |B| * ‖M q‖)
    hs hmeas
    (sourceFreeTimeDensity_integrable_of_majorant
      a t (ha t) M hM (hdom t ht))
    hdiffmeas hdom' hmajor hdiff
  have hmoment :
      (∫ q : LogTorus n,
        -f t q * sourceTimeDensity a t q
          ∂(sourceTorusBaseMeasure n)) =
        -sourceFirstMoment a f t := by
    calc
      (∫ q : LogTorus n,
        -f t q * sourceTimeDensity a t q
          ∂(sourceTorusBaseMeasure n)) =
        ∫ q : LogTorus n,
          -(f t q * sourceTimeDensity a t q)
            ∂(sourceTorusBaseMeasure n) := by
              apply integral_congr_ae
              filter_upwards [] with q
              ring
      _ = -sourceFirstMoment a f t := by
        rw [integral_neg]
        rfl
  change HasDerivAt
    (fun u : ℝ =>
      ∫ q : LogTorus n,
        sourceTimeDensity a u q ∂(sourceTorusBaseMeasure n))
    (-sourceFirstMoment a f t) t
  rw [← hmoment]
  exact h.2

private theorem hasDerivAt_sourceFreeLogPartition_of_majorant
    {n : ℕ}
    (a f : ℝ → LogTorus n → ℝ)
    {t : ℝ} {s : Set ℝ} {B : ℝ}
    (hs : s ∈ 𝓝 t)
    (ha : ∀ u : ℝ, Continuous (a u))
    (hf : ∀ u : ℝ, Continuous (f u))
    (hderiv : ∀ (u : ℝ) (q : LogTorus n),
      HasDerivAt (fun v : ℝ => a v q) (f u q) u)
    (M : LogTorus n → ℝ)
    (hM : Integrable M (sourceTorusBaseMeasure n))
    (hdom : ∀ u ∈ s, ∀ q : LogTorus n,
      sourceTimeDensity a u q ≤ M q)
    (hbound : ∀ u ∈ s, ∀ q : LogTorus n, |f u q| ≤ B)
    (hpart : 0 < sourcePartition a t) :
    HasDerivAt (sourceLogPartition a)
      (sourceLogSlope a f t) t := by
  have hfirst := hasDerivAt_sourceFreePartition_of_majorant
    a f hs ha hf hderiv M hM hdom hbound
  change HasDerivAt
    (fun u : ℝ => -Real.log (sourcePartition a u))
    (sourceFirstMoment a f t / sourcePartition a t) t
  have h := (hfirst.log hpart.ne').neg
  refine (h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  ring

private theorem hasDerivAt_sourceFreeFirstMoment_of_majorant
    {n : ℕ}
    (a f j : ℝ → LogTorus n → ℝ)
    {t : ℝ} {s : Set ℝ} {B J : ℝ}
    (hs : s ∈ 𝓝 t)
    (ha : ∀ u : ℝ, Continuous (a u))
    (hf : ∀ u : ℝ, Continuous (f u))
    (hj : ∀ u : ℝ, Continuous (j u))
    (hderiv : ∀ (u : ℝ) (q : LogTorus n),
      HasDerivAt (fun v : ℝ => a v q) (f u q) u)
    (hfderiv : ∀ (u : ℝ) (q : LogTorus n),
      HasDerivAt (fun v : ℝ => f v q) (j u q) u)
    (M : LogTorus n → ℝ)
    (hM : Integrable M (sourceTorusBaseMeasure n))
    (hdom : ∀ u ∈ s, ∀ q : LogTorus n,
      sourceTimeDensity a u q ≤ M q)
    (hbound : ∀ u ∈ s, ∀ q : LogTorus n, |f u q| ≤ B)
    (hjbound : ∀ u ∈ s, ∀ q : LogTorus n, |j u q| ≤ J) :
    HasDerivAt (sourceFirstMoment a f)
      (sourceAccelerationMoment a j t - sourceSecondMoment a f t) t := by
  have ht : t ∈ s := mem_of_mem_nhds hs
  have hmajor :
      Integrable
        (fun q : LogTorus n => (|J| + |B| ^ 2) * ‖M q‖)
        (sourceTorusBaseMeasure n) :=
    hM.norm.const_mul (|J| + |B| ^ 2)
  have hmeas :
      ∀ᶠ u in 𝓝 t,
        AEStronglyMeasurable
          (fun q : LogTorus n =>
            f u q * sourceTimeDensity a u q)
          (sourceTorusBaseMeasure n) :=
    Filter.Eventually.of_forall fun u =>
      ((hf u).mul
        (Real.continuous_exp.comp (ha u).neg)).aestronglyMeasurable
  have hdiffmeas : AEStronglyMeasurable
      (fun q : LogTorus n =>
        (j t q - f t q ^ 2) * sourceTimeDensity a t q)
      (sourceTorusBaseMeasure n) :=
    (((hj t).sub ((hf t).pow 2)).mul
      (Real.continuous_exp.comp (ha t).neg)).aestronglyMeasurable
  have hdom' :
      ∀ᵐ q ∂(sourceTorusBaseMeasure n),
        ∀ u ∈ s,
          ‖(j u q - f u q ^ 2) * sourceTimeDensity a u q‖ ≤
            (|J| + |B| ^ 2) * ‖M q‖ := by
    filter_upwards [] with q u hu
    have hfabs : |f u q| ≤ |B| :=
      (hbound u hu q).trans (le_abs_self B)
    have hjabs : |j u q| ≤ |J| :=
      (hjbound u hu q).trans (le_abs_self J)
    have hcoef : |j u q - f u q ^ 2| ≤ |J| + |B| ^ 2 := by
      calc
        |j u q - f u q ^ 2| ≤ |j u q| + |f u q ^ 2| :=
          abs_sub _ _
        _ = |j u q| + |f u q| ^ 2 := by rw [abs_pow]
        _ ≤ |J| + |B| ^ 2 :=
          add_le_add hjabs (pow_le_pow_left₀ (abs_nonneg _) hfabs 2)
    change
      |(j u q - f u q ^ 2) * Real.exp (-a u q)| ≤
        (|J| + |B| ^ 2) * ‖M q‖
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul hcoef
      ((hdom u hu q).trans (le_abs_self _))
      (Real.exp_pos _).le (by positivity)
  have hdiff :
      ∀ᵐ q ∂(sourceTorusBaseMeasure n),
        ∀ u ∈ s,
          HasDerivAt
            (fun v : ℝ => f v q * sourceTimeDensity a v q)
            ((j u q - f u q ^ 2) * sourceTimeDensity a u q) u := by
    filter_upwards [] with q u _
    have hprod := (hfderiv u q).fun_mul (hderiv u q).neg.exp
    refine (hprod.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    dsimp [sourceTimeDensity]
    ring
  have hfirstint := sourceFreeWeightedObservable_integrable_of_majorant
    a (f t) t B (ha t) (hf t) M hM (hdom t ht) (hbound t ht)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := sourceTorusBaseMeasure n)
    (F := fun u q => f u q * sourceTimeDensity a u q)
    (F' := fun u q =>
      (j u q - f u q ^ 2) * sourceTimeDensity a u q)
    (bound := fun q => (|J| + |B| ^ 2) * ‖M q‖)
    hs hmeas hfirstint hdiffmeas hdom' hmajor hdiff
  have hjint := sourceFreeWeightedObservable_integrable_of_majorant
    a (j t) t J (ha t) (hj t) M hM (hdom t ht) (hjbound t ht)
  have hsquare : ∀ q : LogTorus n, |f t q ^ 2| ≤ |B| ^ 2 := by
    intro q
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _)
      ((hbound t ht q).trans (le_abs_self B)) 2
  have hsquareint := sourceFreeWeightedObservable_integrable_of_majorant
    a (fun q => f t q ^ 2) t (|B| ^ 2)
    (ha t) ((hf t).pow 2) M hM (hdom t ht) hsquare
  have hmoment :
      (∫ q : LogTorus n,
        (j t q - f t q ^ 2) * sourceTimeDensity a t q
          ∂(sourceTorusBaseMeasure n)) =
        sourceAccelerationMoment a j t - sourceSecondMoment a f t := by
    calc
      (∫ q : LogTorus n,
        (j t q - f t q ^ 2) * sourceTimeDensity a t q
          ∂(sourceTorusBaseMeasure n)) =
        ∫ q : LogTorus n,
          (j t q * sourceTimeDensity a t q -
            f t q ^ 2 * sourceTimeDensity a t q)
              ∂(sourceTorusBaseMeasure n) := by
                apply integral_congr_ae
                filter_upwards [] with q
                ring
      _ = sourceAccelerationMoment a j t - sourceSecondMoment a f t := by
        rw [integral_sub hjint hsquareint]
        rfl
  change HasDerivAt
    (fun u : ℝ =>
      ∫ q : LogTorus n,
        f u q * sourceTimeDensity a u q
          ∂(sourceTorusBaseMeasure n))
    (sourceAccelerationMoment a j t - sourceSecondMoment a f t) t
  rw [← hmoment]
  exact h.2

private theorem hasDerivAt_sourceFreeLogSlope_of_majorant
    {n : ℕ}
    (a f j : ℝ → LogTorus n → ℝ)
    {t : ℝ} {s : Set ℝ} {B J : ℝ}
    (hs : s ∈ 𝓝 t)
    (ha : ∀ u : ℝ, Continuous (a u))
    (hf : ∀ u : ℝ, Continuous (f u))
    (hj : ∀ u : ℝ, Continuous (j u))
    (hderiv : ∀ (u : ℝ) (q : LogTorus n),
      HasDerivAt (fun v : ℝ => a v q) (f u q) u)
    (hfderiv : ∀ (u : ℝ) (q : LogTorus n),
      HasDerivAt (fun v : ℝ => f v q) (j u q) u)
    (M : LogTorus n → ℝ)
    (hM : Integrable M (sourceTorusBaseMeasure n))
    (hdom : ∀ u ∈ s, ∀ q : LogTorus n,
      sourceTimeDensity a u q ≤ M q)
    (hbound : ∀ u ∈ s, ∀ q : LogTorus n, |f u q| ≤ B)
    (hjbound : ∀ u ∈ s, ∀ q : LogTorus n, |j u q| ≤ J)
    (hpart : 0 < sourcePartition a t) :
    HasDerivAt (sourceLogSlope a f)
      (sourceAccelerationMoment a j t / sourcePartition a t -
        sourceMomentVariance a f t) t := by
  have hp := hasDerivAt_sourceFreePartition_of_majorant
    a f hs ha hf hderiv M hM hdom hbound
  have hm := hasDerivAt_sourceFreeFirstMoment_of_majorant
    a f j hs ha hf hj hderiv hfderiv M hM hdom hbound hjbound
  change HasDerivAt
    (fun u : ℝ => sourceFirstMoment a f u / sourcePartition a u)
    (sourceAccelerationMoment a j t / sourcePartition a t -
      (sourceSecondMoment a f t / sourcePartition a t -
        (sourceFirstMoment a f t / sourcePartition a t) ^ 2)) t
  refine (hm.fun_div hp hpart.ne').congr_deriv ?_
  field_simp [hpart.ne']
  ring

private theorem zero_lt_of_mem_positiveHalfBall
    {t u : ℝ} (ht : 0 < t)
    (hu : u ∈ Metric.ball t (t / 2)) : 0 < u := by
  have habs : |u - t| < t / 2 := by
    simpa only [mem_ball, Real.dist_eq] using hu
  have hlower := (abs_lt.mp habs).1
  linarith

private theorem sourceFreeLogCurvature_nonneg_of_complexBrascamp_and_schur
    {n : ℕ}
    (a f j : ℝ → LogTorus n → ℝ)
    (E : LogTorus n → ℝ)
    (t B J : ℝ)
    (ha : Continuous (a t))
    (hf : Continuous (f t))
    (hj : Continuous (j t))
    (hpart : 0 < sourcePartition a t)
    (hprob : IsProbabilityMeasure (sourceProbability a t))
    (hfbound : ∀ q : LogTorus n, |f t q| ≤ B)
    (hjbound : ∀ q : LogTorus n, |j t q| ≤ J)
    (hEint : Integrable E (sourceProbability a t))
    (hcomplexBrascamp :
      sourceProbabilityVariance a t (f t) ≤
        sourceProbabilityMean a t E)
    (hschur : ∀ q : LogTorus n, E q ≤ j t q) :
    0 ≤ sourceAccelerationMoment a j t / sourcePartition a t -
      sourceMomentVariance a f t := by
  let : IsProbabilityMeasure (sourceProbability a t) := hprob
  have hvelocity := sourceFreeProbability_memLp_two_of_bound
    a (f t) t B hprob hf hfbound
  have hacceleration := sourceFreeProbability_memLp_two_of_bound
    a (j t) t J hprob hj hjbound
  have hjint := hacceleration.integrable (by norm_num)
  apply sub_nonneg.mpr
  calc
    sourceMomentVariance a f t =
        sourceProbabilityVariance a t (f t) :=
      (sourceFreeProbabilityVariance_eq_momentVariance
        a f t ha hf hpart hprob hvelocity).symm
    _ ≤ sourceProbabilityMean a t E := hcomplexBrascamp
    _ ≤ sourceProbabilityMean a t (j t) :=
      MeasureTheory.integral_mono hEint hjint hschur
    _ = sourceAccelerationMoment a j t / sourcePartition a t :=
      sourceFreeProbabilityMean_acceleration_eq_moment
        a j t ha hpart

private theorem convexOn_sourceFreeLogPartition_Ioi_of_complexBrascamp_and_schur
    {n : ℕ}
    (a f j E : ℝ → LogTorus n → ℝ)
    (ha : ∀ t : ℝ, Continuous (a t))
    (hf : ∀ t : ℝ, Continuous (f t))
    (hj : ∀ t : ℝ, Continuous (j t))
    (hderiv : ∀ (t : ℝ) (q : LogTorus n),
      HasDerivAt (fun u : ℝ => a u q) (f t q) t)
    (hfderiv : ∀ (t : ℝ) (q : LogTorus n),
      HasDerivAt (fun u : ℝ => f u q) (j t q) t)
    (M : LogTorus n → ℝ)
    (hM : Integrable M (sourceTorusBaseMeasure n))
    (hdom : ∀ (t : ℝ), 0 < t → ∀ q : LogTorus n,
      sourceTimeDensity a t q ≤ M q)
    (hpart : ∀ (t : ℝ), 0 < t → 0 < sourcePartition a t)
    (hprob : ∀ (t : ℝ), 0 < t →
      IsProbabilityMeasure (sourceProbability a t))
    (hfbound : ∀ (t : ℝ), 0 < t → ∃ B : ℝ,
      ∀ u ∈ Metric.ball t (t / 2),
        ∀ q : LogTorus n, |f u q| ≤ B)
    (hjbound : ∀ (t : ℝ), 0 < t → ∃ J : ℝ,
      ∀ u ∈ Metric.ball t (t / 2),
        ∀ q : LogTorus n, |j u q| ≤ J)
    (hEint : ∀ (t : ℝ), 0 < t →
      Integrable (E t) (sourceProbability a t))
    (hcomplexBrascamp : ∀ (t : ℝ), 0 < t →
      sourceProbabilityVariance a t (f t) ≤
        sourceProbabilityMean a t (E t))
    (hschur : ∀ (t : ℝ), 0 < t →
      ∀ q : LogTorus n, E t q ≤ j t q) :
    ConvexOn ℝ (Set.Ioi 0) (sourceLogPartition a) := by
  have hfirst : ∀ (t : ℝ), 0 < t →
      HasDerivAt (sourceLogPartition a) (sourceLogSlope a f t) t := by
    intro t ht
    obtain ⟨B, hB⟩ := hfbound t ht
    apply hasDerivAt_sourceFreeLogPartition_of_majorant
      a f (Metric.ball_mem_nhds t (half_pos ht))
      ha hf hderiv M hM
      (fun u hu q => hdom u
        (zero_lt_of_mem_positiveHalfBall ht hu) q)
      hB (hpart t ht)
  have hsecond : ∀ (t : ℝ), 0 < t →
      HasDerivAt (sourceLogSlope a f)
        (sourceAccelerationMoment a j t / sourcePartition a t -
          sourceMomentVariance a f t) t := by
    intro t ht
    obtain ⟨B, hB⟩ := hfbound t ht
    obtain ⟨J, hJ⟩ := hjbound t ht
    exact hasDerivAt_sourceFreeLogSlope_of_majorant
      a f j (Metric.ball_mem_nhds t (half_pos ht))
      ha hf hj hderiv hfderiv M hM
      (fun u hu q => hdom u
        (zero_lt_of_mem_positiveHalfBall ht hu) q)
      hB hJ (hpart t ht)
  have hcurvature : ∀ (t : ℝ), 0 < t →
      0 ≤ sourceAccelerationMoment a j t / sourcePartition a t -
        sourceMomentVariance a f t := by
    intro t ht
    obtain ⟨B, hB⟩ := hfbound t ht
    obtain ⟨J, hJ⟩ := hjbound t ht
    have htball : t ∈ Metric.ball t (t / 2) :=
      Metric.mem_ball_self (half_pos ht)
    exact sourceFreeLogCurvature_nonneg_of_complexBrascamp_and_schur
      a f j (E t) t B J
      (ha t) (hf t) (hj t) (hpart t ht) (hprob t ht)
      (hB t htball) (hJ t htball)
      (hEint t ht) (hcomplexBrascamp t ht) (hschur t ht)
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi (0 : ℝ))
    (fun t ht => (hfirst t ht).continuousAt.continuousWithinAt)
    (f' := sourceLogSlope a f)
    (f'' := fun t =>
      sourceAccelerationMoment a j t / sourcePartition a t -
        sourceMomentVariance a f t)
  · intro t ht
    have ht' : 0 < t := by simpa only [interior_Ioi, mem_Ioi] using ht
    exact (hfirst t ht').hasDerivWithinAt
  · intro t ht
    have ht' : 0 < t := by simpa only [interior_Ioi, mem_Ioi] using ht
    exact (hsecond t ht').hasDerivWithinAt
  · intro t ht
    have ht' : 0 < t := by simpa only [interior_Ioi, mem_Ioi] using ht
    exact hcurvature t ht'

private def momentWeakHolomorphicStrictJointPhysicalMixedCover
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ)
    (z : LogSpace n) : ℂ :=
  (jointSourceCoverVelocity
    (momentWeakHolomorphicStrictJointCoverWeight
      K F htransport p ε k)
    (z, (t / 2 : ℂ)) : ℂ)

private theorem contDiff_momentWeakHolomorphicStrictJointPhysicalMixedCover
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ) :
    ContDiff ℝ 3
      (momentWeakHolomorphicStrictJointPhysicalMixedCover
        K F htransport p ε k t) := by
  let G : SourceJointComplexCover n → ℝ :=
    momentWeakHolomorphicStrictJointCoverWeight
      K F htransport p ε k
  have hG : ContDiff ℝ 4 G :=
    (contDiff_infty.mp
      (contDiff_momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)) 4
  have hv : ContDiff ℝ 3 (jointSourceCoverVelocity G) := by
    unfold jointSourceCoverVelocity
    exact (hG.fderiv_right (m := 3) (by norm_num)).clm_apply
      contDiff_const
  exact Complex.ofRealCLM.contDiff.comp
    (hv.comp (contDiff_id.prodMk contDiff_const))

private theorem momentWeakHolomorphicStrictJointPhysicalMixedCover_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ)
    (d : Fin n → ℤ) :
    Function.Periodic
      (momentWeakHolomorphicStrictJointPhysicalMixedCover
        K F htransport p ε k t)
      (imaginaryShift d) := by
  intro z
  change
    (jointSourceCoverVelocity
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)
      (z + imaginaryShift d, (t / 2 : ℂ)) : ℂ) =
    (jointSourceCoverVelocity
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)
      (z, (t / 2 : ℂ)) : ℂ)
  have h := jointSourceCoverVelocity_spatial_periodic
    (momentWeakHolomorphicStrictJointCoverWeight_spatial_periodic
      K F htransport p ε k) d (z, (t / 2 : ℂ))
  simpa only [Prod.mk_add_mk, add_zero] using
    congrArg Complex.ofReal h

private def momentWeakHolomorphicStrictJointPhysicalCenteredCover
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ)
    (z : LogSpace n) : ℂ :=
  momentWeakHolomorphicStrictJointPhysicalMixedCover
    K F htransport p ε k t z -
  (sourceProbabilityMean
    (momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p ε k) t
    (jointSourceTorusVelocity
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k) t) : ℂ)

private theorem contDiff_momentWeakHolomorphicStrictJointPhysicalCenteredCover
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ) :
    ContDiff ℝ 3
      (momentWeakHolomorphicStrictJointPhysicalCenteredCover
        K F htransport p ε k t) := by
  exact
    (contDiff_momentWeakHolomorphicStrictJointPhysicalMixedCover
      K F htransport p ε k t).sub contDiff_const

private theorem momentWeakHolomorphicStrictJointPhysicalCenteredCover_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ)
    (d : Fin n → ℤ) :
    Function.Periodic
      (momentWeakHolomorphicStrictJointPhysicalCenteredCover
        K F htransport p ε k t)
      (imaginaryShift d) := by
  intro z
  unfold momentWeakHolomorphicStrictJointPhysicalCenteredCover
  rw [momentWeakHolomorphicStrictJointPhysicalMixedCover_periodic
    K F htransport p ε k t d z]

private def momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ)
    (q : LogTorus n) : ℂ :=
  ((jointSourceTorusVelocity
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k) t q -
    sourceProbabilityMean
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k) t
      (jointSourceTorusVelocity
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t) : ℝ) : ℂ)

private theorem torusScalarRepresentative_momentWeakHolomorphicStrictJointPhysicalCenteredCover
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ)
    (q : LogTorus n) :
    torusScalarRepresentative
      (momentWeakHolomorphicStrictJointPhysicalCenteredCover
        K F htransport p ε k t) q =
    momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
      K F htransport p ε k t q := by
  unfold torusScalarRepresentative
    momentWeakHolomorphicStrictJointPhysicalCenteredCover
    momentWeakHolomorphicStrictJointPhysicalMixedCover
    momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
  rw [jointSourceTorusVelocity_eq_cover]
  change
    (jointSourceCoverVelocity
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)
      (sourceTorusCoverPoint q, (t / 2 : ℂ)) : ℂ) - _ =
    ((jointSourceCoverVelocity
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)
      (sourceJointTimeEmbedding (sourceTorusCoverPoint q) t) -
      sourceProbabilityMean
        (momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k) t
        (jointSourceTorusVelocity
          (momentWeakHolomorphicStrictJointCoverWeight
            K F htransport p ε k) t) : ℝ) : ℂ)
  simp only [sourceJointTimeEmbedding, Complex.ofReal_sub]

private def momentWeakHolomorphicStrictJointPhysicalMixedRow
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ)
    (q : LogTorus n) : Fin n → ℂ :=
  fun i => sourceTorusBarPartial
    (momentWeakHolomorphicStrictJointPhysicalMixedCover
      K F htransport p ε k t) i q

private theorem momentWeakHolomorphicStrictJointPhysicalMixedRow_eq_cover
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ)
    (q : LogTorus n) :
    momentWeakHolomorphicStrictJointPhysicalMixedRow
      K F htransport p ε k t q =
    sourceJointCoverAntiholomorphicVelocityGradient
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)
      (t / 2 : ℂ) (sourceTorusCoverPoint q) := by
  funext i
  rfl

private theorem barPartialRepresentative_centeredCover
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ)
    (q : LogTorus n) :
    torusFunctionBarPartialRepresentative
      (momentWeakHolomorphicStrictJointPhysicalCenteredCover
        K F htransport p ε k t) q =
      WithLp.toLp 2
        (momentWeakHolomorphicStrictJointPhysicalMixedRow
          K F htransport p ε k t q) := by
  ext i
  change
    coverRepresentative
      (fun z => barPartialCoordinate
        (momentWeakHolomorphicStrictJointPhysicalCenteredCover
          K F htransport p ε k t) z i) q.1 q.2 =
    coverRepresentative
      (fun z => barPartialCoordinate
        (momentWeakHolomorphicStrictJointPhysicalMixedCover
          K F htransport p ε k t) z i) q.1 q.2
  congr 1
  funext z
  unfold momentWeakHolomorphicStrictJointPhysicalCenteredCover
  rw [barPartial_sub
    ((contDiff_momentWeakHolomorphicStrictJointPhysicalMixedCover
      K F htransport p ε k t).of_le (by norm_num))
    contDiff_const z i]
  simp only [barPartialCoordinate, fderiv_fun_const, Pi.zero_apply, _root_.zero_apply, mul_zero,
    add_zero, zero_div, sub_zero]

private def momentWeakHolomorphicStrictJointPhysicalRowEnergy
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ)
    (q : LogTorus n) : ℝ :=
  sourceComplexRowSchurEnergyDensity
    (angularTorusComplexHessianMatrix
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k t) q)
    (momentWeakHolomorphicStrictJointPhysicalMixedRow
      K F htransport p ε k t q)

private theorem momentWeakHolomorphicStrictJointPhysicalRowEnergy_le_acceleration
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (t : ℝ) (q : LogTorus n) :
    momentWeakHolomorphicStrictJointPhysicalRowEnergy
      K F htransport p ε k t q ≤
    jointSourceTorusAcceleration
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k) t q := by
  unfold momentWeakHolomorphicStrictJointPhysicalRowEnergy
  rw [angularTorusComplexHessianMatrix_momentWeakHolomorphicStrictJointTorusWeight_eq,
    momentWeakHolomorphicStrictJointPhysicalMixedRow_eq_cover,
    jointSourceTorusAcceleration_eq_cover]
  exact momentWeakHolomorphicStrictJointCover_rowSchurEnergy_le_acceleration
    K F htransport p ε hε₀ hε₁ k (t / 2 : ℂ)
      (sourceTorusCoverPoint q)

private theorem momentWeakHolomorphicStrictJointPhysicalRowEnergy_nonneg
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (t : ℝ) (q : LogTorus n) :
    0 ≤ momentWeakHolomorphicStrictJointPhysicalRowEnergy
      K F htransport p ε k t q := by
  exact sourceComplexRowSchurEnergyDensity_nonneg
    (angularTorusComplexHessianMatrix_momentWeakHolomorphicStrictJointTorusWeight_posDef
      K F htransport p ε hε₀ hε₁ k t q)
    (momentWeakHolomorphicStrictJointPhysicalMixedRow
      K F htransport p ε k t q)

private theorem continuous_momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ) :
    Continuous
      (momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
        K F htransport p ε k t) := by
  exact Complex.continuous_ofReal.comp
    ((continuous_jointSourceTorusVelocity
      ((contDiff_infty.mp
        (contDiff_momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k)) 2)
      (momentWeakHolomorphicStrictJointCoverWeight_spatial_periodic
        K F htransport p ε k) t).sub continuous_const)

private theorem momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_angular_memLp
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (t : ℝ)
    {B : ℝ}
    (hB : ∀ q : LogTorus n,
      |jointSourceTorusVelocity
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t q| ≤ B) :
    MemLp
      (momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
        K F htransport p ε k t) 2
      (angularWeightedTorusMeasure
        (momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k t)) := by
  let : IsFiniteMeasure
      (angularWeightedTorusMeasure
        (momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k t)) :=
    momentWeakHolomorphicStrictJointWeightedMeasure_isFinite
      K F htransport p k t hε₀ hε₁
  apply MemLp.of_bound
    (continuous_momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
      K F htransport p ε k t).aestronglyMeasurable
    (B + |sourceProbabilityMean
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k) t
      (jointSourceTorusVelocity
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t)|)
  filter_upwards [] with q
  unfold momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact (abs_sub _ _).trans (add_le_add (hB q) (le_refl _))

private theorem centeredVelocity_probability_integral_eq_zero
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (t : ℝ)
    {B : ℝ}
    (hB : ∀ q : LogTorus n,
      |jointSourceTorusVelocity
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t q| ≤ B) :
    (∫ q : LogTorus n,
      momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
        K F htransport p ε k t q
        ∂(sourceProbability
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k) t)) = 0 := by
  let a : ℝ → LogTorus n → ℝ :=
    momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p ε k
  let ν : Measure (LogTorus n) := sourceProbability a t
  let : IsProbabilityMeasure ν :=
    momentWeakHolomorphicStrictJointProbability_isProbability
      K F htransport p k t hε₀ hε₁
  let v : LogTorus n → ℝ :=
    jointSourceTorusVelocity
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k) t
  let A : ℝ := sourceProbabilityMean a t v
  have hv : Integrable v ν := by
    apply Integrable.of_bound
      (continuous_jointSourceTorusVelocity
        ((contDiff_infty.mp
          (contDiff_momentWeakHolomorphicStrictJointCoverWeight
            K F htransport p ε k)) 2)
        (momentWeakHolomorphicStrictJointCoverWeight_spatial_periodic
          K F htransport p ε k) t).aestronglyMeasurable B
    filter_upwards [] with q
    exact hB q
  have hreal : (∫ q : LogTorus n, v q - A ∂ν) = 0 := by
    rw [integral_sub hv (integrable_const A)]
    simp only [sourceProbabilityMean, integral_const, probReal_univ, smul_eq_mul, one_mul, sub_self,
      ν, A]
  change (∫ q : LogTorus n, ((v q - A : ℝ) : ℂ) ∂ν) = 0
  rw [integral_complex_ofReal, hreal]
  norm_num

private theorem momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_angular_integral_eq_zero
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (t : ℝ)
    {B : ℝ}
    (hB : ∀ q : LogTorus n,
      |jointSourceTorusVelocity
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t q| ≤ B) :
    (∫ q : LogTorus n,
      momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
        K F htransport p ε k t q
        ∂(angularWeightedTorusMeasure
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t))) = 0 := by
  let a : ℝ → LogTorus n → ℝ :=
    momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p ε k
  let Z : ℝ := sourcePartition a t
  have hZ : 0 < Z :=
    momentWeakHolomorphicStrictJointPartition_pos
      K F htransport p k t hε₀ hε₁
  have hzero :=
    centeredVelocity_probability_integral_eq_zero
      K F htransport p ε hε₀ hε₁ k t hB
  rw [momentWeakHolomorphicStrictJointProbability_eq_smul_weighted
    K F htransport p k t hε₀ hε₁,
    integral_smul_measure] at hzero
  have hfactor : ((ENNReal.ofReal Z)⁻¹).toReal ≠ 0 := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ.le]
    exact inv_ne_zero hZ.ne'
  exact (smul_eq_zero.mp hzero).resolve_left hfactor

private theorem momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_mem_resolventDefect_closure
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (t : ℝ)
    {B : ℝ}
    (hB : ∀ q : LogTorus n,
      |jointSourceTorusVelocity
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t q| ≤ B) :
    (momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_angular_memLp
      K F htransport p ε hε₀ hε₁ k t hB).toLp
        (momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
          K F htransport p ε k t) ∈
      ((ContinuousLinearMap.id ℂ
        (angularWeightedScalarL2
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t)) -
        angularWeakScalarResolventCLM
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t)).range).topologicalClosure := by
  apply momentWeakHolomorphicStrictJoint_centered_mem_resolventDefect_range_closure
    K F htransport p k t hε₀ hε₁
  rw [← momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_angular_integral_eq_zero
    K F htransport p ε hε₀ hε₁ k t hB]
  exact integral_congr_ae
    (momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_angular_memLp
      K F htransport p ε hε₀ hε₁ k t hB).coeFn_toLp

private theorem continuous_angularSourceFreeInverseRootGradientField
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    {U : LogSpace n → ℂ}
    (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ,
      Function.Periodic U (imaginaryShift d)) :
    Continuous (angularSourceFreeInverseRootGradientField a U) := by
  have hroot := continuous_angularMatrixSquareRoot_inverse
    (continuous_angularTorusComplexHessianMatrix ha2) hH
  have hrow := continuous_torusFunctionBarPartialRepresentative_of_periodic
    (hU.of_le (by norm_num)) hperiod
  change Continuous
    (fun q : LogTorus n =>
      WithLp.toLp 2 (fun i : Fin n =>
        ∑ j : Fin n,
          ((angularMatrixSquareRoot
            (angularTorusComplexHessianMatrix a) q)⁻¹) i j *
            conj (torusFunctionBarPartialRepresentative U q j)))
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp
  apply continuous_pi
  intro i
  apply continuous_finsetSum
  intro j _
  exact (hroot.matrix_elem i j).mul
    (Complex.continuous_conj.comp
      ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) j).comp hrow))

private theorem momentWeakHolomorphicStrictJointPhysicalRowEnergy_eq_inverseRoot_norm_sq
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (t : ℝ) (q : LogTorus n) :
    momentWeakHolomorphicStrictJointPhysicalRowEnergy
      K F htransport p ε k t q =
    ‖angularSourceFreeInverseRootGradientField
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k t)
      (momentWeakHolomorphicStrictJointPhysicalCenteredCover
        K F htransport p ε k t) q‖ ^ 2 := by
  unfold momentWeakHolomorphicStrictJointPhysicalRowEnergy
  rw [sourceComplexRowSchurEnergyDensity_eq_inverseSquareRoot_norm_sq
    (angularTorusComplexHessianMatrix_momentWeakHolomorphicStrictJointTorusWeight_posDef
      K F htransport p ε hε₀ hε₁ k t q)]
  unfold angularSourceFreeInverseRootGradientField
  rw [barPartialRepresentative_centeredCover
    K F htransport p ε k t q]
  rfl

private theorem momentWeakHolomorphicStrictJointPhysicalInverseRoot_angular_memLp
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (t : ℝ)
    {J : ℝ}
    (hJ : ∀ q : LogTorus n,
      |jointSourceTorusAcceleration
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t q| ≤ J) :
    MemLp
      (angularSourceFreeInverseRootGradientField
        (momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k t)
        (momentWeakHolomorphicStrictJointPhysicalCenteredCover
          K F htransport p ε k t)) 2
      (angularWeightedTorusMeasure
        (momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k t)) := by
  let a : LogTorus n → ℝ :=
    momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p ε k t
  let U : LogSpace n → ℂ :=
    momentWeakHolomorphicStrictJointPhysicalCenteredCover
      K F htransport p ε k t
  let : IsFiniteMeasure (angularWeightedTorusMeasure a) :=
    momentWeakHolomorphicStrictJointWeightedMeasure_isFinite
      K F htransport p k t hε₀ hε₁
  have hcontinuous :
      Continuous (angularSourceFreeInverseRootGradientField a U) :=
    continuous_angularSourceFreeInverseRootGradientField
      ((contDiff_infty.mp
        (contDiff_angularCoverPotential_momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k t)) 2)
      (angularTorusComplexHessianMatrix_momentWeakHolomorphicStrictJointTorusWeight_posDef
        K F htransport p ε hε₀ hε₁ k t)
      (contDiff_momentWeakHolomorphicStrictJointPhysicalCenteredCover
        K F htransport p ε k t)
      (momentWeakHolomorphicStrictJointPhysicalCenteredCover_periodic
        K F htransport p ε k t)
  apply MemLp.of_bound hcontinuous.aestronglyMeasurable (Real.sqrt |J|)
  filter_upwards [] with q
  apply (sq_le_sq₀ (norm_nonneg _)
    (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (abs_nonneg J)]
  rw [← momentWeakHolomorphicStrictJointPhysicalRowEnergy_eq_inverseRoot_norm_sq
    K F htransport p ε hε₀ hε₁ k t q]
  exact (momentWeakHolomorphicStrictJointPhysicalRowEnergy_le_acceleration
    K F htransport p ε hε₀ hε₁ k t q).trans
      ((le_abs_self _).trans ((hJ q).trans (le_abs_self J)))

private theorem momentWeakHolomorphicStrictJointPhysicalCenteredAngularL2_norm_sq
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (t : ℝ) {B : ℝ}
    (hB : ∀ q : LogTorus n,
      |jointSourceTorusVelocity
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t q| ≤ B) :
    ‖(momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_angular_memLp
      K F htransport p ε hε₀ hε₁ k t hB).toLp
        (momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
          K F htransport p ε k t)‖ ^ 2 =
    ∫ q : LogTorus n,
      (jointSourceTorusVelocity
          (momentWeakHolomorphicStrictJointCoverWeight
            K F htransport p ε k) t q -
        sourceProbabilityMean
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k) t
          (jointSourceTorusVelocity
            (momentWeakHolomorphicStrictJointCoverWeight
              K F htransport p ε k) t)) ^ 2
        ∂(angularWeightedTorusMeasure
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t)) := by
  rw [complexLp_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards
    [(momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_angular_memLp
      K F htransport p ε hε₀ hε₁ k t hB).coeFn_toLp]
      with q hq
  rw [hq]
  unfold momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

private theorem momentWeakHolomorphicStrictJointPhysicalInverseRootAngularL2_norm_sq
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (t : ℝ) {J : ℝ}
    (hJ : ∀ q : LogTorus n,
      |jointSourceTorusAcceleration
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t q| ≤ J) :
    ‖(momentWeakHolomorphicStrictJointPhysicalInverseRoot_angular_memLp
      K F htransport p ε hε₀ hε₁ k t hJ).toLp
        (angularSourceFreeInverseRootGradientField
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t)
          (momentWeakHolomorphicStrictJointPhysicalCenteredCover
            K F htransport p ε k t))‖ ^ 2 =
    ∫ q : LogTorus n,
      momentWeakHolomorphicStrictJointPhysicalRowEnergy
        K F htransport p ε k t q
        ∂(angularWeightedTorusMeasure
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t)) := by
  rw [complexLp_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards
    [(momentWeakHolomorphicStrictJointPhysicalInverseRoot_angular_memLp
      K F htransport p ε hε₀ hε₁ k t hJ).coeFn_toLp]
      with q hq
  rw [hq]
  exact
    (momentWeakHolomorphicStrictJointPhysicalRowEnergy_eq_inverseRoot_norm_sq
      K F htransport p ε hε₀ hε₁ k t q).symm

private theorem momentWeakHolomorphicStrictJointPhysicalVariance_eq_angular_L2_norm_sq_div_partition
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (t : ℝ) {B : ℝ}
    (hB : ∀ q : LogTorus n,
      |jointSourceTorusVelocity
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t q| ≤ B) :
    sourceProbabilityVariance
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k) t
      (jointSourceTorusVelocity
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t) =
    (sourcePartition
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k) t)⁻¹ *
      ‖(momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_angular_memLp
        K F htransport p ε hε₀ hε₁ k t hB).toLp
          (momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
            K F htransport p ε k t)‖ ^ 2 := by
  have hpart := momentWeakHolomorphicStrictJointPartition_pos
    K F htransport p k t hε₀ hε₁
  unfold sourceProbabilityVariance
  rw [momentWeakHolomorphicStrictJointProbability_eq_smul_weighted
    K F htransport p k t hε₀ hε₁,
    integral_smul_measure,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hpart.le,
    smul_eq_mul]
  rw [← momentWeakHolomorphicStrictJointPhysicalCenteredAngularL2_norm_sq
    K F htransport p ε hε₀ hε₁ k t hB]

private theorem rowEnergy_probabilityMean_eq_L2_norm_sq_div_partition
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (t : ℝ) {J : ℝ}
    (hJ : ∀ q : LogTorus n,
      |jointSourceTorusAcceleration
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t q| ≤ J) :
    sourceProbabilityMean
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k) t
      (momentWeakHolomorphicStrictJointPhysicalRowEnergy
        K F htransport p ε k t) =
    (sourcePartition
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k) t)⁻¹ *
      ‖(momentWeakHolomorphicStrictJointPhysicalInverseRoot_angular_memLp
        K F htransport p ε hε₀ hε₁ k t hJ).toLp
          (angularSourceFreeInverseRootGradientField
            (momentWeakHolomorphicStrictJointTorusWeight
              K F htransport p ε k t)
            (momentWeakHolomorphicStrictJointPhysicalCenteredCover
              K F htransport p ε k t))‖ ^ 2 := by
  have hpart := momentWeakHolomorphicStrictJointPartition_pos
    K F htransport p k t hε₀ hε₁
  unfold sourceProbabilityMean
  rw [momentWeakHolomorphicStrictJointProbability_eq_smul_weighted
    K F htransport p k t hε₀ hε₁,
    integral_smul_measure,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hpart.le,
    smul_eq_mul]
  rw [← momentWeakHolomorphicStrictJointPhysicalInverseRootAngularL2_norm_sq
    K F htransport p ε hε₀ hε₁ k t hJ]

private theorem momentWeakHolomorphicStrictJointPhysicalBrascamp
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (t : ℝ)
    {B J : ℝ}
    (hB : ∀ q : LogTorus n,
      |jointSourceTorusVelocity
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t q| ≤ B)
    (hJ : ∀ q : LogTorus n,
      |jointSourceTorusAcceleration
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t q| ≤ J) :
    sourceProbabilityVariance
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k) t
      (jointSourceTorusVelocity
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) t) ≤
    sourceProbabilityMean
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k) t
      (momentWeakHolomorphicStrictJointPhysicalRowEnergy
        K F htransport p ε k t) := by
  let a : LogTorus n → ℝ :=
    momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p ε k t
  let U : LogSpace n → ℂ :=
    momentWeakHolomorphicStrictJointPhysicalCenteredCover
      K F htransport p ε k t
  let hv :=
    momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_angular_memLp
      K F htransport p ε hε₀ hε₁ k t hB
  have hUeq : torusScalarRepresentative U =
      momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
        K F htransport p ε k t := by
    funext q
    exact
      torusScalarRepresentative_momentWeakHolomorphicStrictJointPhysicalCenteredCover
        K F htransport p ε k t q
  have hu : MemLp (torusScalarRepresentative U) 2
      (angularWeightedTorusMeasure a) := by
    rw [hUeq]
    exact hv
  let hr :=
    momentWeakHolomorphicStrictJointPhysicalInverseRoot_angular_memLp
      K F htransport p ε hε₀ hε₁ k t hJ
  have hclosure :
      hu.toLp (torusScalarRepresentative U) ∈
        ((ContinuousLinearMap.id ℂ (angularWeightedScalarL2 a) -
          angularWeakScalarResolventCLM a).range).topologicalClosure := by
    simpa only [hUeq] using
      momentWeakHolomorphicStrictJointPhysicalCenteredVelocity_mem_resolventDefect_closure
        K F htransport p ε hε₀ hε₁ k t hB
  have hnorm := angularSourceFreeBrascampLieb_of_mem_resolventDefect_closure
    (continuous_momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p ε k t)
    ((contDiff_infty.mp
      (contDiff_angularCoverPotential_momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k t)) 3)
    (angularTorusComplexHessianMatrix_momentWeakHolomorphicStrictJointTorusWeight_posDef
      K F htransport p ε hε₀ hε₁ k t)
    (contDiff_momentWeakHolomorphicStrictJointPhysicalCenteredCover
      K F htransport p ε k t)
    (momentWeakHolomorphicStrictJointPhysicalCenteredCover_periodic
      K F htransport p ε k t)
    hu hr hclosure
  have hleft : hu.toLp (torusScalarRepresentative U) =
      hv.toLp
        (momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
          K F htransport p ε k t) := by
    apply MemLp.toLp_congr
    filter_upwards [] with q
    exact congrFun hUeq q
  have hnorm' :
      ‖hv.toLp
        (momentWeakHolomorphicStrictJointPhysicalCenteredVelocity
          K F htransport p ε k t)‖ ≤
      ‖hr.toLp (angularSourceFreeInverseRootGradientField a U)‖ := by
    change
      ‖hu.toLp (torusScalarRepresentative U)‖ ≤
        ‖hr.toLp (angularSourceFreeInverseRootGradientField a U)‖
      at hnorm
    rw [hleft] at hnorm
    exact hnorm
  rw [momentWeakHolomorphicStrictJointPhysicalVariance_eq_angular_L2_norm_sq_div_partition
    K F htransport p ε hε₀ hε₁ k t hB,
    rowEnergy_probabilityMean_eq_L2_norm_sq_div_partition
      K F htransport p ε hε₀ hε₁ k t hJ]
  exact mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm')
    (inv_nonneg.mpr
      (momentWeakHolomorphicStrictJointPartition_pos
        K F htransport p k t hε₀ hε₁).le)

private theorem continuous_momentWeakHolomorphicStrictJointPhysicalRowEnergy
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (t : ℝ) :
    Continuous
      (momentWeakHolomorphicStrictJointPhysicalRowEnergy
        K F htransport p ε k t) := by
  have hroot := continuous_angularSourceFreeInverseRootGradientField
    ((contDiff_infty.mp
      (contDiff_angularCoverPotential_momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k t)) 2)
    (angularTorusComplexHessianMatrix_momentWeakHolomorphicStrictJointTorusWeight_posDef
      K F htransport p ε hε₀ hε₁ k t)
    (contDiff_momentWeakHolomorphicStrictJointPhysicalCenteredCover
      K F htransport p ε k t)
    (momentWeakHolomorphicStrictJointPhysicalCenteredCover_periodic
      K F htransport p ε k t)
  have heq :
      momentWeakHolomorphicStrictJointPhysicalRowEnergy
        K F htransport p ε k t =
      fun q : LogTorus n =>
        ‖angularSourceFreeInverseRootGradientField
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t)
          (momentWeakHolomorphicStrictJointPhysicalCenteredCover
            K F htransport p ε k t) q‖ ^ 2 := by
    funext q
    exact
      momentWeakHolomorphicStrictJointPhysicalRowEnergy_eq_inverseRoot_norm_sq
        K F htransport p ε hε₀ hε₁ k t q
  rw [heq]
  exact hroot.norm.pow 2

private theorem convexOn_momentWeakHolomorphicStrictJointLogPartition_Ioi_of_timeBounds
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (k : ℕ)
    (hvbound : ∀ (t : ℝ), 0 < t → ∃ B : ℝ,
      ∀ u ∈ Metric.ball t (t / 2),
        ∀ q : LogTorus n,
          |jointSourceTorusVelocity
            (momentWeakHolomorphicStrictJointCoverWeight
              K F htransport p ε k) u q| ≤ B)
    (hjbound : ∀ (t : ℝ), 0 < t → ∃ J : ℝ,
      ∀ u ∈ Metric.ball t (t / 2),
        ∀ q : LogTorus n,
          |jointSourceTorusAcceleration
            (momentWeakHolomorphicStrictJointCoverWeight
              K F htransport p ε k) u q| ≤ J) :
    ConvexOn ℝ (Set.Ioi 0)
      (sourceLogPartition
        (momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k)) := by
  let G : SourceJointComplexCover n → ℝ :=
    momentWeakHolomorphicStrictJointCoverWeight
      K F htransport p ε k
  let a : ℝ → LogTorus n → ℝ :=
    momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p ε k
  let f : ℝ → LogTorus n → ℝ := jointSourceTorusVelocity G
  let j : ℝ → LogTorus n → ℝ := jointSourceTorusAcceleration G
  let E : ℝ → LogTorus n → ℝ :=
    momentWeakHolomorphicStrictJointPhysicalRowEnergy
      K F htransport p ε k
  have hG : ContDiff ℝ 2 G :=
    (contDiff_infty.mp
      (contDiff_momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)) 2
  have hGp : ∀ d : Fin n → ℤ,
      Function.Periodic G (imaginaryShift d, (0 : ℂ)) :=
    momentWeakHolomorphicStrictJointCoverWeight_spatial_periodic
      K F htransport p ε k
  change ConvexOn ℝ (Set.Ioi 0) (sourceLogPartition a)
  apply convexOn_sourceFreeLogPartition_Ioi_of_complexBrascamp_and_schur
    a f j E
    (fun t => continuous_momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p ε k t)
    (fun t => continuous_jointSourceTorusVelocity hG hGp t)
    (fun t => continuous_jointSourceTorusAcceleration hG hGp t)
    (fun t q => hasDerivAt_jointSourceTorusWeight hG t q)
    (fun t q => hasDerivAt_jointSourceTorusVelocity hG t q)
    (momentWeakHolomorphicUniformDensityMajorant K F htransport)
    (integrable_momentWeakHolomorphicUniformDensityMajorant
      K F htransport)
  · intro t ht q
    exact exp_neg_momentWeakHolomorphicStrictJointTorusWeight_le_uniform
      K F htransport p k ht hε₀.le hε₁ q
  · intro t _
    exact momentWeakHolomorphicStrictJointPartition_pos
      K F htransport p k t hε₀ hε₁
  · intro t _
    exact momentWeakHolomorphicStrictJointProbability_isProbability
      K F htransport p k t hε₀ hε₁
  · exact hvbound
  · exact hjbound
  · intro t ht
    obtain ⟨J, hJ⟩ := hjbound t ht
    let : IsProbabilityMeasure (sourceProbability a t) :=
      momentWeakHolomorphicStrictJointProbability_isProbability
        K F htransport p k t hε₀ hε₁
    have htball : t ∈ Metric.ball t (t / 2) :=
      Metric.mem_ball_self (half_pos ht)
    have hpoint : ∀ q : LogTorus n,
        |E t q| ≤ J := by
      intro q
      rw [abs_of_nonneg
        (momentWeakHolomorphicStrictJointPhysicalRowEnergy_nonneg
          K F htransport p ε hε₀ hε₁ k t q)]
      exact
        (momentWeakHolomorphicStrictJointPhysicalRowEnergy_le_acceleration
          K F htransport p ε hε₀ hε₁ k t q).trans
          ((le_abs_self _).trans (hJ t htball q))
    exact (sourceFreeProbability_memLp_two_of_bound a (E t) t J
      (momentWeakHolomorphicStrictJointProbability_isProbability
        K F htransport p k t hε₀ hε₁)
      (continuous_momentWeakHolomorphicStrictJointPhysicalRowEnergy
        K F htransport p ε hε₀ hε₁ k t)
      hpoint).integrable (by norm_num)
  · intro t ht
    obtain ⟨B, hB⟩ := hvbound t ht
    obtain ⟨J, hJ⟩ := hjbound t ht
    have htball : t ∈ Metric.ball t (t / 2) :=
      Metric.mem_ball_self (half_pos ht)
    exact momentWeakHolomorphicStrictJointPhysicalBrascamp
      K F htransport p ε hε₀ hε₁ k t
      (hB t htball) (hJ t htball)
  · intro t _ q
    exact momentWeakHolomorphicStrictJointPhysicalRowEnergy_le_acceleration
      K F htransport p ε hε₀ hε₁ k t q

private theorem convexOn_momentWeakHolomorphicStrictJointLogPartition_Ioi
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (k : ℕ) :
    ConvexOn ℝ (Set.Ioi 0)
      (sourceLogPartition
        (momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k)) := by
  apply
    convexOn_momentWeakHolomorphicStrictJointLogPartition_Ioi_of_timeBounds
      K F htransport p ε hε₀ hε₁ k
  · intro t _
    exact exists_momentWeakHolomorphicStrictJointTorusVelocity_local_bound
      K F htransport p ε hε₀.le hε₁ k t
  · intro t _
    exact exists_momentWeakHolomorphicStrictJointTorusAcceleration_local_bound
      K F htransport p ε hε₀.le hε₁ k t

end BergmanJetHolomorphicPhysicalLogConvexity

namespace BergmanJetJointHolomorphicConvexTransfer

open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert MomentOptimizer MomentTargetGeodesic MomentFirstVariation
open MomentRegularity BergmanJetTorusEnvelope BergmanJetPartitionEndpoint
open BergmanJetJointHolomorphicStrictSchur BergmanJetJointHolomorphicPhysicalApproximation
open JetEnvelopeSlopeConvergence LogPartitionConvexity
open scoped BigOperators ENNReal Topology

private theorem exp_neg_canonicalScale_mul_volume_le_momentBodyPartition
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) {t : ℝ} (ht : 0 < t) :
    Real.exp (-(BodyScale.canonicalScale K * t)) *
        normalizedVolume K.carrier ≤
      momentBodyPartition K p t := by
  have hzero :=
    integrable_exp_neg_momentBodyTorusWeight K p 0
  have htime :=
    integrable_exp_neg_momentBodyTorusWeight K p t
  calc
    Real.exp (-(BodyScale.canonicalScale K * t)) *
        normalizedVolume K.carrier =
      Real.exp (-(BodyScale.canonicalScale K * t)) *
        momentBodyPartition K p 0 := by
          rw [momentBodyPartition_zero]
    _ = ∫ q : LogTorus n,
          Real.exp (-(BodyScale.canonicalScale K * t)) *
            Real.exp (-momentBodyTorusWeight K p 0 q)
              ∂(sourceTorusBaseMeasure n) := by
          rw [momentBodyPartition_eq_integral,
            MeasureTheory.integral_const_mul]
    _ ≤ ∫ q : LogTorus n,
          Real.exp (-momentBodyTorusWeight K p t q)
            ∂(sourceTorusBaseMeasure n) := by
          apply MeasureTheory.integral_mono
            (hzero.const_mul
              (Real.exp
                (-(BodyScale.canonicalScale K * t))))
            htime
          intro q
          change
            Real.exp (-(BodyScale.canonicalScale K * t)) *
                Real.exp (-momentBodyTorusWeight K p 0 q) ≤
              Real.exp (-momentBodyTorusWeight K p t q)
          rw [← Real.exp_add,
            momentBodyTorusWeight_zero]
          apply Real.exp_le_exp.mpr
          have hupper := momentTorusEnvelopeTimeSlice_le_normalized_add
            K (momentBodyOptimizer K)
              (momentBodyOptimizer_transport K)
              p q ht
          change
            momentBodyTorusWeight K p t q ≤
              momentNormalizedPotential
                (momentBodyOptimizer K) q.1 +
                BodyScale.canonicalScale K * t at hupper
          linarith
    _ = momentBodyPartition K p t :=
      (momentBodyPartition_eq_integral K p t).symm

private theorem exp_neg_canonicalScale_mul_le_momentBodyNormalizedPartition
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) {t : ℝ} (ht : 0 < t) :
    Real.exp (-(BodyScale.canonicalScale K * t)) ≤
      momentBodyNormalizedPartition K p t := by
  unfold momentBodyNormalizedPartition
  apply (le_div_iff₀ K.volume_pos).mpr
  exact exp_neg_canonicalScale_mul_volume_le_momentBodyPartition
    K p ht

private theorem momentBodyLogPartition_le_canonicalScale_mul_of_pos
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) {t : ℝ} (ht : 0 < t) :
    momentBodyLogPartition K p t ≤
      BodyScale.canonicalScale K * t := by
  have hlower :=
    exp_neg_canonicalScale_mul_le_momentBodyNormalizedPartition
      K p ht
  have hleft :
      0 < Real.exp (-(BodyScale.canonicalScale K * t)) :=
    Real.exp_pos _
  have hright := momentBodyNormalizedPartition_pos K p t
  have hlog := Real.strictMonoOn_log.monotoneOn hleft hright hlower
  rw [Real.log_exp] at hlog
  unfold momentBodyLogPartition
  linarith

private theorem convexOn_Ici_of_convexOn_Ioi_and_zero_linear_upper
    (f : ℝ → ℝ) (C : ℝ)
    (hfzero : f 0 = 0)
    (hfconv : ConvexOn ℝ (Set.Ioi 0) f)
    (hupper : ∀ t : ℝ, 0 < t → f t ≤ C * t) :
    ConvexOn ℝ (Set.Ici 0) f := by
  have hsegment :
      ∀ (y a b : ℝ), 0 < y → 0 ≤ a → 0 ≤ b → a + b = 1 →
        f (a * 0 + b * y) ≤ a * f 0 + b * f y := by
    intro y a b hy ha hb hab
    rcases hb.eq_or_lt with hbzero | hbpos
    · have hb0 : b = 0 := hbzero.symm
      have ha1 : a = 1 := by linarith
      simp only [ha1, mul_zero, hb0, zero_mul, add_zero, hfzero, Std.le_refl]
    · let e : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
      have he : Tendsto e atTop (𝓝 (0 : ℝ)) := by
        exact tendsto_one_div_add_atTop_nhds_zero_nat
      have hepos (j : ℕ) : 0 < e j := by
        dsimp [e]
        positivity
      have hby : 0 < b * y := mul_pos hbpos hy
      have hcontinuity : ContinuousAt f (b * y) :=
        (hfconv.continuousOn isOpen_Ioi).continuousAt
          (isOpen_Ioi.mem_nhds hby)
      have harg :
          Tendsto
            (fun j : ℕ => a * e j + b * y)
            atTop (𝓝 (b * y)) := by
        simpa only [mul_zero, zero_add] using
          (he.const_mul a).add
            (tendsto_const_nhds :
              Tendsto (fun _ : ℕ => b * y)
                atTop (𝓝 (b * y)))
      have hleft := hcontinuity.tendsto.comp harg
      have hright :
          Tendsto
            (fun j : ℕ => a * (C * e j) + b * f y)
            atTop (𝓝 (a * f 0 + b * f y)) := by
        have hCe := he.const_mul C
        have haCe := hCe.const_mul a
        have hconst :
            Tendsto (fun _ : ℕ => b * f y)
              atTop (𝓝 (b * f y)) :=
          tendsto_const_nhds
        simpa only [hfzero, mul_zero, zero_add] using haCe.add hconst
      simp only [mul_zero, zero_add]
      apply le_of_tendsto_of_tendsto hleft hright
      exact Filter.Eventually.of_forall fun j => by
        have hcv := hfconv.2 (hepos j) hy ha hb hab
        have hu := hupper (e j) (hepos j)
        change
          f (a * e j + b * y) ≤
            a * (C * e j) + b * f y
        calc
          f (a * e j + b * y) ≤
              a * f (e j) + b * f y := by
                simpa only [smul_eq_mul] using hcv
          _ ≤ a * (C * e j) + b * f y := by
            gcongr
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  rcases hx.eq_or_lt with hxzero | hxpos
  · have hx0 : x = 0 := hxzero.symm
    subst x
    rcases hy.eq_or_lt with hyzero | hypos
    · have hy0 : y = 0 := hyzero.symm
      subst y
      simp only [smul_eq_mul, mul_zero, add_zero, hfzero, Std.le_refl]
    · simpa only [smul_eq_mul, mul_zero, zero_add, ge_iff_le] using
        hsegment y a b hypos ha hb hab
  · rcases hy.eq_or_lt with hyzero | hypos
    · have hy0 : y = 0 := hyzero.symm
      subst y
      have hswap := hsegment x b a hxpos hb ha (by linarith)
      simpa only [smul_eq_mul, mul_zero, add_zero, ge_iff_le, add_comm] using hswap
    · simpa only [smul_eq_mul] using
        hfconv.2 hxpos hypos ha hb hab

private theorem convexOn_momentWeakHolomorphicEnvelopeLogPartition_Ioi_of_strict
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 (0 : ℝ)))
    (hε₀ : ∀ k : ℕ, 0 ≤ ε k)
    (hε₁ : ∀ k : ℕ, ε k ≤ 1)
    (hstrict : ∀ k : ℕ,
      ConvexOn ℝ (Set.Ioi 0)
        (sourceLogPartition
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p (ε k) k))) :
    ConvexOn ℝ (Set.Ioi 0)
      (sourceLogPartition
        (fun (t : ℝ) (q : LogTorus n) =>
          momentTorusEnvelopeTimeSlice K F htransport p q t)) := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy a b ha hb hab
  change 0 < x at hx
  change 0 < y at hy
  have hm : 0 < a * x + b * y := by
    rcases ha.eq_or_lt with hazero | hapos
    · have ha0 : a = 0 := hazero.symm
      have hb1 : b = 1 := by linarith
      simp only [ha0, zero_mul, hb1, one_mul, zero_add, hy]
    · nlinarith [mul_pos hapos hx, mul_nonneg hb hy.le]
  have hmid :=
    tendsto_momentWeakHolomorphicStrictJointLogPartition
      K F htransport p ε hε hε₀ hε₁ hm
  have hleft :=
    tendsto_momentWeakHolomorphicStrictJointLogPartition
      K F htransport p ε hε hε₀ hε₁ hx
  have hright :=
    tendsto_momentWeakHolomorphicStrictJointLogPartition
      K F htransport p ε hε hε₀ hε₁ hy
  change
    sourceLogPartition
      (fun (t : ℝ) (q : LogTorus n) =>
        momentTorusEnvelopeTimeSlice K F htransport p q t)
      (a * x + b * y) ≤
      a * sourceLogPartition
        (fun (t : ℝ) (q : LogTorus n) =>
          momentTorusEnvelopeTimeSlice K F htransport p q t) x +
      b * sourceLogPartition
        (fun (t : ℝ) (q : LogTorus n) =>
          momentTorusEnvelopeTimeSlice K F htransport p q t) y
  apply le_of_tendsto_of_tendsto hmid
    ((hleft.const_mul a).add (hright.const_mul b))
  exact Filter.Eventually.of_forall fun k => by
    simpa only [smul_eq_mul] using
      (hstrict k).2 hx hy ha hb hab

private theorem convexOn_momentBodyLogPartition_Ioi_of_holomorphicStrict
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 (0 : ℝ)))
    (hε₀ : ∀ k : ℕ, 0 ≤ ε k)
    (hε₁ : ∀ k : ℕ, ε k ≤ 1)
    (hstrict : ∀ k : ℕ,
      ConvexOn ℝ (Set.Ioi 0)
        (sourceLogPartition
          (momentWeakHolomorphicStrictJointTorusWeight
            K (momentBodyOptimizer K)
              (momentBodyOptimizer_transport K)
              p (ε k) k))) :
    ConvexOn ℝ (Set.Ioi 0)
      (momentBodyLogPartition K p) := by
  have hweak :=
    convexOn_momentWeakHolomorphicEnvelopeLogPartition_Ioi_of_strict
      K (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K)
        p ε hε hε₀ hε₁ hstrict
  have hconstant :
      ConvexOn ℝ (Set.Ioi (0 : ℝ))
        (fun _ : ℝ => Real.log (normalizedVolume K.carrier)) :=
    convexOn_const
      (Real.log (normalizedVolume K.carrier))
      (convex_Ioi (0 : ℝ))
  have hadd := hweak.add hconstant
  have heq :
      momentBodyLogPartition K p =
        (fun t : ℝ =>
          sourceLogPartition
            (fun (u : ℝ) (q : LogTorus n) =>
              momentTorusEnvelopeTimeSlice
                K (momentBodyOptimizer K)
                  (momentBodyOptimizer_transport K)
                  p q u) t +
            Real.log (normalizedVolume K.carrier)) := by
    funext t
    rw [momentBodyLogPartition_eq_sourceLogPartition_add_log_volume]
    rfl
  rw [heq]
  exact hadd

private theorem convexOn_momentBodyLogPartition_Ici_of_holomorphicStrict
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 (0 : ℝ)))
    (hε₀ : ∀ k : ℕ, 0 ≤ ε k)
    (hε₁ : ∀ k : ℕ, ε k ≤ 1)
    (hstrict : ∀ k : ℕ,
      ConvexOn ℝ (Set.Ioi 0)
        (sourceLogPartition
          (momentWeakHolomorphicStrictJointTorusWeight
            K (momentBodyOptimizer K)
              (momentBodyOptimizer_transport K)
              p (ε k) k))) :
    ConvexOn ℝ (Set.Ici 0)
      (momentBodyLogPartition K p) := by
  apply convexOn_Ici_of_convexOn_Ioi_and_zero_linear_upper
    (momentBodyLogPartition K p)
    (BodyScale.canonicalScale K)
    (momentBodyLogPartition_zero K p)
    (convexOn_momentBodyLogPartition_Ioi_of_holomorphicStrict
      K p ε hε hε₀ hε₁ hstrict)
  intro t ht
  exact momentBodyLogPartition_le_canonicalScale_mul_of_pos
    K p ht

end BergmanJetJointHolomorphicConvexTransfer

namespace BergmanJetJointHolomorphicUnconditionalBodyConvexity

open Set Function Filter
open TorusCharacters BergmanJetPartitionEndpoint BergmanJetHolomorphicPhysicalLogConvexity
open BergmanJetJointHolomorphicConvexTransfer
open scoped Topology

private theorem convexOn_momentBodyLogPartition_Ici
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) :
    ConvexOn ℝ (Set.Ici 0)
      (momentBodyLogPartition K p) := by
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hεpos (k : ℕ) : 0 < ε k := by
    dsimp [ε]
    positivity
  have hεle (k : ℕ) : ε k ≤ 1 := by
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have hnonneg : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    dsimp [ε]
    simpa only [one_div, ge_iff_le, ne_eq, one_ne_zero, not_false_eq_true,
      div_self] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hk
  have hε : Tendsto ε atTop (𝓝 (0 : ℝ)) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  apply convexOn_momentBodyLogPartition_Ici_of_holomorphicStrict
    K p ε hε (fun k => (hεpos k).le) hεle
  intro k
  exact convexOn_momentWeakHolomorphicStrictJointLogPartition_Ioi
    K (momentBodyOptimizer K)
    (momentBodyOptimizer_transport K)
    p (ε k) (hεpos k) (hεle k) k

end BergmanJetJointHolomorphicUnconditionalBodyConvexity

namespace BergmanJetLocalGrowth

open Set Function Filter MeasureTheory Module Metric Asymptotics
open BergmanMonomials BergmanDiagonalBasisIndependence GlobalBergmanKernelBound AdaptedBergmanBasis
open MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentWeakBergman
open BergmanJetBasis MomentWeakGlobalKernel BergmanJetGeodesic BergmanJetProfileBridge
open BergmanJetRealGeodesic JetEnvelopeLocalGrowth LaurentJetMultiplicityBridge
open scoped BigOperators Topology ENNReal InnerProductSpace

private theorem analyticAt_momentHolomorphicRepresentative
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (s : momentMonomialSpan K hk F htransport)
    (p : TorusCharacters.LogSpace n) :
    AnalyticAt ℂ
      (momentHolomorphicRepresentative K hk F htransport s) p := by
  classical
  unfold momentHolomorphicRepresentative
  rw [LinearMap.comp_apply, Finsupp.linearCombination_apply]
  unfold Finsupp.sum
  apply Finset.analyticAt_sum
  intro u _
  exact
    (LaurentJetSeparatedness.analyticAt_normalizedHolomorphicMonomial
      K hk (momentNormalizedPotential F) u p).const_smul

private theorem contDiff_momentHolomorphicRepresentative
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (s : momentMonomialSpan K hk F htransport) :
    ContDiff ℂ ⊤
      (momentHolomorphicRepresentative K hk F htransport s) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact (analyticAt_momentHolomorphicRepresentative
    K hk F htransport s p).contDiffAt

private theorem momentHolomorphicJetMap_apply_eq_iteratedFDeriv
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (j : ℕ)
    (s : momentMonomialSpan K hk F htransport)
    (α : JetCounting.JetIndexLT n j) :
    momentHolomorphicJetMap K hk F htransport p j s α =
      (iteratedFDeriv ℂ (∑ i, α.val i)
        (momentHolomorphicRepresentative K hk F htransport s) p)
          (fun q => Pi.single
            (multiIndexCoordinate α.val q) (1 : ℂ)) := by
  classical
  unfold momentHolomorphicJetMap
    momentHolomorphicRepresentative
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  unfold Finsupp.sum
  simp only [Finset.sum_apply, Pi.smul_apply]
  change
    (∑ u ∈ ((momentLatticeMonomialBasis
        K hk F htransport).repr s).support,
      ((momentLatticeMonomialBasis
        K hk F htransport).repr s u) •
        holomorphicMonomialJet K hk
          (momentNormalizedPotential F) p u α.val) =
      (iteratedFDeriv ℂ (∑ i, α.val i)
        (∑ u ∈ ((momentLatticeMonomialBasis
            K hk F htransport).repr s).support,
          ((momentLatticeMonomialBasis
            K hk F htransport).repr s u) •
            normalizedHolomorphicMonomial K hk
              (momentNormalizedPotential F) u) p)
        (fun q => Pi.single (multiIndexCoordinate α.val q) (1 : ℂ))
  have hderiv :
      iteratedFDeriv ℂ (∑ i, α.val i)
        (∑ u ∈ ((momentLatticeMonomialBasis
            K hk F htransport).repr s).support,
          ((momentLatticeMonomialBasis
            K hk F htransport).repr s u) •
            normalizedHolomorphicMonomial K hk
              (momentNormalizedPotential F) u) p =
        ∑ u ∈ ((momentLatticeMonomialBasis
            K hk F htransport).repr s).support,
          iteratedFDeriv ℂ (∑ i, α.val i)
            (((momentLatticeMonomialBasis
              K hk F htransport).repr s u) •
              normalizedHolomorphicMonomial K hk
                (momentNormalizedPotential F) u) p := by
    apply iteratedFDeriv_sum_apply
    intro u _
    exact
      (LaurentJetSeparatedness.analyticAt_normalizedHolomorphicMonomial
        K hk (momentNormalizedPotential F) u p).contDiffAt.const_smul
          ((momentLatticeMonomialBasis
            K hk F htransport).repr s u)
  rw [hderiv]
  simp only [_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro u _
  rw [iteratedFDeriv_const_smul_apply
    (LaurentJetSeparatedness.analyticAt_normalizedHolomorphicMonomial
      K hk (momentNormalizedPotential F) u p).contDiffAt]
  simp only [holomorphicMonomialJet, smul_eq_mul, smul_apply]

private theorem momentHolomorphicRepresentative_iteratedFDeriv_comp_perm
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (s : momentMonomialSpan K hk F htransport)
    {r : ℕ} (v : Fin r → TorusCharacters.LogSpace n)
    (σ : Equiv.Perm (Fin r)) :
    (iteratedFDeriv ℂ r
      (momentHolomorphicRepresentative K hk F htransport s) p)
        (v ∘ σ) =
    (iteratedFDeriv ℂ r
      (momentHolomorphicRepresentative K hk F htransport s) p) v := by
  exact (contDiff_momentHolomorphicRepresentative
    K hk F htransport s).contDiffAt.iteratedFDeriv_comp_perm v σ

private theorem moment_iteratedFDeriv_coordinate_eq_zero_of_mem_jetFiltration
    {n k r : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (s : momentMonomialSpan K hk F htransport)
    (q : Fin r → Fin n) (α : Fin n → ℕ)
    (hdegree : (∑ i, α i) = r)
    (hcount : ∀ i : Fin n,
      Fintype.card {a : Fin r // q a = i} = α i)
    (hs : s ∈ momentJetFiltration
      K hk F htransport p (r + 1)) :
    (iteratedFDeriv ℂ r
      (momentHolomorphicRepresentative K hk F htransport s) p)
      (fun a => Pi.single (q a) (1 : ℂ)) = 0 := by
  classical
  subst r
  obtain ⟨σ, hσ⟩ := exists_multiIndexCoordinate_perm α q hcount
  let β : JetCounting.JetIndexLT n ((∑ i, α i) + 1) :=
    ⟨α, Nat.lt_succ_self _⟩
  change momentHolomorphicJetMap
    K hk F htransport p ((∑ i, α i) + 1) s = 0 at hs
  have hcanonical :
      (iteratedFDeriv ℂ (∑ i, α i)
        (momentHolomorphicRepresentative K hk F htransport s) p)
        (fun a => Pi.single (multiIndexCoordinate α a) (1 : ℂ)) = 0 := by
    calc
      (iteratedFDeriv ℂ (∑ i, α i)
        (momentHolomorphicRepresentative K hk F htransport s) p)
          (fun a => Pi.single (multiIndexCoordinate α a) (1 : ℂ)) =
        momentHolomorphicJetMap
          K hk F htransport p ((∑ i, α i) + 1) s β :=
          (momentHolomorphicJetMap_apply_eq_iteratedFDeriv
            K hk F htransport p ((∑ i, α i) + 1) s β).symm
      _ = 0 := congrFun hs β
  calc
    (iteratedFDeriv ℂ (∑ i, α i)
      (momentHolomorphicRepresentative K hk F htransport s) p)
        (fun a => Pi.single (q a) (1 : ℂ)) =
      (iteratedFDeriv ℂ (∑ i, α i)
        (momentHolomorphicRepresentative K hk F htransport s) p)
          ((fun a => Pi.single (multiIndexCoordinate α a)
            (1 : ℂ)) ∘ σ) := by
              congr 1
              funext a
              simpa only [Function.comp_apply] using
                congrArg (fun i : Fin n => Pi.single i (1 : ℂ)) (hσ a)
    _ = (iteratedFDeriv ℂ (∑ i, α i)
      (momentHolomorphicRepresentative K hk F htransport s) p)
        (fun a => Pi.single (multiIndexCoordinate α a) (1 : ℂ)) :=
          momentHolomorphicRepresentative_iteratedFDeriv_comp_perm
            K hk F htransport p s _ σ
    _ = 0 := hcanonical

private theorem moment_iteratedFDeriv_eq_zero_of_mem_jetFiltration
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (s : momentMonomialSpan K hk F htransport)
    (r : ℕ)
    (hs : s ∈ momentJetFiltration
      K hk F htransport p (r + 1)) :
    iteratedFDeriv ℂ r
      (momentHolomorphicRepresentative K hk F htransport s) p = 0 := by
  classical
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear
    (fun _ : Fin r => Pi.basisFun ℂ (Fin n))
  intro q
  simp only [Pi.basisFun_apply]
  exact moment_iteratedFDeriv_coordinate_eq_zero_of_mem_jetFiltration
    K hk F htransport p s q (coordinateMultiplicity q)
      (sum_coordinateMultiplicity q) (fun _ => rfl) hs

private theorem momentSimultaneousJetBasis_mem_truncatedJetFiltration
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (i : Fin (bergmanDimension K k)) :
    momentSimultaneousJetBasis K hk F htransport p i ∈
      momentJetFiltration K hk F htransport p
        (momentTruncatedJetOrder K hk F htransport p N i) := by
  classical
  let S : Finset ℕ := (Finset.range N).filter (fun j =>
    momentSimultaneousJetBasis K hk F htransport p i ∈
      momentJetFiltration K hk F htransport p (j + 1))
  change momentSimultaneousJetBasis K hk F htransport p i ∈
    momentJetFiltration K hk F htransport p S.card
  by_cases hzero : S.card = 0
  · rw [hzero, momentJetFiltration_zero]
    simp only [Submodule.mem_top]
  · have hpos : 0 < S.card := Nat.pos_of_ne_zero hzero
    by_contra hnot
    have hsub : S ⊆ Finset.range (S.card - 1) := by
      intro j hj
      have hmem :
          momentSimultaneousJetBasis K hk F htransport p i ∈
            momentJetFiltration K hk F htransport p (j + 1) :=
        (Finset.mem_filter.mp hj).2
      apply Finset.mem_range.mpr
      by_contra hlt
      have hle : S.card ≤ j + 1 := by omega
      exact hnot
        (momentJetFiltration_antitone
          K hk F htransport p hle hmem)
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_range] at hcard
    omega

private theorem momentHolomorphicRepresentative_isLittleO_of_mem_jetFiltration
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (s : momentMonomialSpan K hk F htransport)
    (j : ℕ)
    (hs : s ∈ momentJetFiltration
      K hk F htransport p (j + 1)) :
    (fun z : TorusCharacters.LogSpace n =>
      momentHolomorphicRepresentative K hk F htransport s z -
        momentHolomorphicRepresentative K hk F htransport s p)
      =o[𝓝 p]
        (fun z : TorusCharacters.LogSpace n => ‖z - p‖ ^ j) := by
  apply isLittleO_norm_pow_of_iteratedFDeriv_zero
    _ (contDiff_momentHolomorphicRepresentative
      K hk F htransport s) p j
  intro i hi
  apply moment_iteratedFDeriv_eq_zero_of_mem_jetFiltration
    K hk F htransport p s i
  exact momentJetFiltration_antitone
    K hk F htransport p (show i + 1 ≤ j + 1 by omega) hs

private theorem momentHolomorphicRepresentative_schwarz_of_mem_jetFiltration
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (s : momentMonomialSpan K hk F htransport)
    (j : ℕ)
    (hs : s ∈ momentJetFiltration K hk F htransport p j)
    (R B : ℝ)
    (hbound : ∀ z ∈ Metric.ball p R,
      ‖momentHolomorphicRepresentative
        K hk F htransport s z‖ ≤ B)
    (z : TorusCharacters.LogSpace n)
    (hz : z ∈ Metric.ball p R) :
    ‖momentHolomorphicRepresentative K hk F htransport s z‖ ≤
      B * (dist z p / R) ^ j := by
  let f : TorusCharacters.LogSpace n → ℂ :=
    momentHolomorphicRepresentative K hk F htransport s
  cases j with
  | zero =>
      simpa only [pow_zero, mul_one, ge_iff_le] using hbound z hz
  | succ j =>
      have hmemone : s ∈ momentJetFiltration
          K hk F htransport p 1 :=
        momentJetFiltration_antitone K hk F htransport p
          (show 1 ≤ j + 1 by omega) hs
      have hderzero :=
        moment_iteratedFDeriv_eq_zero_of_mem_jetFiltration
          K hk F htransport p s 0 hmemone
      have hfzero : f p = 0 := by
        apply norm_eq_zero.mp
        have hn := congrArg norm hderzero
        simpa only [norm_eq_zero, norm_iteratedFDeriv_zero, norm_zero, f] using hn
      have hmaps : Set.MapsTo f (Metric.ball p R)
          (Metric.closedBall (f p) B) := by
        intro w hw
        rw [Metric.mem_closedBall, hfzero, dist_zero_right]
        exact hbound w hw
      have hsmall :
          (fun w : TorusCharacters.LogSpace n => f w - f p)
            =o[𝓝 p]
              (fun w : TorusCharacters.LogSpace n =>
                ‖w - p‖ ^ j) :=
        momentHolomorphicRepresentative_isLittleO_of_mem_jetFiltration
          K hk F htransport p s j hs
      have hd : DifferentiableOn ℂ f (Metric.ball p R) :=
        (differentiable_momentHolomorphicRepresentative
          K hk F htransport s).differentiableOn
      have hsch :=
        Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO
          hd hmaps hsmall hz
      simpa only [ge_iff_le, hfzero, dist_zero_right, f] using hsch

private def momentLocalCoverPotential {n : ℕ}
    (K : CenteredBody n) (F : SourceFiniteEnergyPotential K)
    (z : TorusCharacters.LogSpace n) : ℝ :=
  momentNormalizedPotential F (realLogCoordinate z)

private theorem continuous_momentLocalCoverPotential
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K) :
    Continuous (momentLocalCoverPotential K F) := by
  unfold momentLocalCoverPotential
  apply (continuous_momentNormalizedPotential F).comp
    (f := realLogCoordinate)
  unfold realLogCoordinate
  fun_prop

private def momentLocalPotentialMaximum {n : ℕ}
    (K : CenteredBody n) (F : SourceFiniteEnergyPotential K)
    (p : TorusCharacters.LogSpace n) (R : ℝ) : ℝ :=
  sSup (momentLocalCoverPotential K F '' Metric.closedBall p R)

private theorem momentLocalPotential_image_bddAbove
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (p : TorusCharacters.LogSpace n) (R : ℝ) :
    BddAbove (momentLocalCoverPotential K F ''
      Metric.closedBall p R) := by
  exact ((isCompact_closedBall p R).image
    (continuous_momentLocalCoverPotential K F)).bddAbove

private theorem momentLocalCoverPotential_le_localMaximum
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (p : TorusCharacters.LogSpace n) (R : ℝ)
    (z : TorusCharacters.LogSpace n)
    (hz : z ∈ Metric.closedBall p R) :
    momentLocalCoverPotential K F z ≤
      momentLocalPotentialMaximum K F p R := by
  apply le_csSup (momentLocalPotential_image_bddAbove K F p R)
  exact ⟨z, hz, rfl⟩

private theorem momentJetBasisRepresentative_norm_sq_le_diagonalKernel
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : TorusCharacters.LogSpace n)
    (i : Fin (bergmanDimension K k)) :
    ‖momentHolomorphicRepresentative K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p i) z‖ ^ 2 ≤
      diagonalKernel K k (momentNormalizedPotential F)
        (realLogCoordinate z) := by
  have hsum := Finset.single_le_sum
    (fun j _ => momentHolomorphicBasisWeight_nonneg K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p) z j)
    (Finset.mem_univ i)
  rw [sum_momentHolomorphicBasisWeight_eq_diagonalKernel
    K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p) z] at hsum
  simpa only [ge_iff_le, momentHolomorphicBasisWeight, Complex.normSq_eq_norm_sq] using hsum

private theorem eventually_momentJetBasisRepresentative_local_bound
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (R : ℝ) :
    ∀ᶠ k : ℕ in atTop, ∀ (hk : 0 < k)
      (i : Fin (bergmanDimension K k))
      (z : TorusCharacters.LogSpace n),
      z ∈ Metric.ball p R →
        ‖momentHolomorphicRepresentative K hk F htransport
          (momentSimultaneousJetBasis K hk F htransport p i) z‖ ≤
          Real.sqrt
            (Real.exp ((k : ℝ) * momentLocalPotentialMaximum K F p R) *
              globalKernelPolynomialConstant K * (k : ℝ) ^ (2 * n)) := by
  filter_upwards
    [eventually_momentNormalized_diagonalKernel_le_polynomial
      K F htransport] with k hglobal hk i z hz
  have hpot : momentNormalizedPotential F (realLogCoordinate z) ≤
      momentLocalPotentialMaximum K F p R :=
    momentLocalCoverPotential_le_localMaximum K F p R z
      (Metric.ball_subset_closedBall hz)
  have hdiag := hglobal (realLogCoordinate z)
  have hdim := momentJetBasisRepresentative_norm_sq_le_diagonalKernel
    K hk F htransport p z i
  apply Real.le_sqrt_of_sq_le
  calc
    ‖momentHolomorphicRepresentative K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p i) z‖ ^ 2 ≤
      diagonalKernel K k (momentNormalizedPotential F)
        (realLogCoordinate z) := hdim
    _ ≤ Real.exp ((k : ℝ) *
          momentNormalizedPotential F (realLogCoordinate z)) *
            globalKernelPolynomialConstant K * (k : ℝ) ^ (2 * n) := hdiag
    _ ≤ Real.exp ((k : ℝ) * momentLocalPotentialMaximum K F p R) *
          globalKernelPolynomialConstant K * (k : ℝ) ^ (2 * n) := by
      gcongr
      exact (globalKernelPolynomialConstant_pos K).le

private theorem eventually_momentJetBasisRepresentative_local_schwarz
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (R : ℝ) :
    ∀ᶠ k : ℕ in atTop, ∀ (hk : 0 < k)
      (N : ℕ) (i : Fin (bergmanDimension K k))
      (z : TorusCharacters.LogSpace n),
      z ∈ Metric.ball p R →
        ‖momentHolomorphicRepresentative K hk F htransport
          (momentSimultaneousJetBasis K hk F htransport p i) z‖ ≤
          Real.sqrt
            (Real.exp ((k : ℝ) * momentLocalPotentialMaximum K F p R) *
              globalKernelPolynomialConstant K * (k : ℝ) ^ (2 * n)) *
            (dist z p / R) ^
              momentTruncatedJetOrder K hk F htransport p N i := by
  filter_upwards
    [eventually_momentJetBasisRepresentative_local_bound
      K F htransport p R] with k hbound hk N i z hz
  exact momentHolomorphicRepresentative_schwarz_of_mem_jetFiltration
    K hk F htransport p
      (momentSimultaneousJetBasis K hk F htransport p i)
      (momentTruncatedJetOrder K hk F htransport p N i)
      (momentSimultaneousJetBasis_mem_truncatedJetFiltration
        K hk F htransport p N i)
      R _ (fun w hw => hbound hk i w hw) z hz

private theorem eventually_momentJetBasisWeight_exp_le_local
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (R : ℝ) (hR : 0 < R) :
    ∀ᶠ k : ℕ in atTop, ∀ (hk : 0 < k)
      (N : ℕ) (i : Fin (bergmanDimension K k))
      (z : TorusCharacters.LogSpace n)
      (t : ℝ), 0 ≤ t →
        dist z p < R * Real.exp (-t / 2) →
          momentHolomorphicBasisWeight K hk F htransport
            (momentSimultaneousJetBasis K hk F htransport p) z i *
              Real.exp (t *
                (momentTruncatedJetOrder
                  K hk F htransport p N i : ℝ)) ≤
            Real.exp
              ((k : ℝ) * momentLocalPotentialMaximum K F p R) *
                globalKernelPolynomialConstant K * (k : ℝ) ^ (2 * n) := by
  filter_upwards
    [eventually_momentJetBasisRepresentative_local_schwarz
      K F htransport p R]
    with k hsch hk N i z t ht hshrink
  let A : ℝ :=
    Real.exp ((k : ℝ) * momentLocalPotentialMaximum K F p R) *
      globalKernelPolynomialConstant K * (k : ℝ) ^ (2 * n)
  let q : ℝ := dist z p / R
  let j : ℕ := momentTruncatedJetOrder
    K hk F htransport p N i
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg (Real.exp_pos _).le
        (globalKernelPolynomialConstant_pos K).le)
      (pow_nonneg (Nat.cast_nonneg k) _)
  have hexp : Real.exp (-t / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hball : z ∈ Metric.ball p R := by
    apply Metric.mem_ball.mpr
    have hb := mul_le_mul_of_nonneg_left hexp hR.le
    linarith
  have hsection :
      ‖momentHolomorphicRepresentative K hk F htransport
        (momentSimultaneousJetBasis
          K hk F htransport p i) z‖ ≤
        Real.sqrt A * q ^ j := by
    simpa [A, q, j] using hsch hk N i z hball
  have hq : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg dist_nonneg hR.le
  have hsq :
      ‖momentHolomorphicRepresentative K hk F htransport
        (momentSimultaneousJetBasis
          K hk F htransport p i) z‖ ^ 2 ≤
        A * (q ^ 2) ^ j := by
    calc
      ‖momentHolomorphicRepresentative K hk F htransport
        (momentSimultaneousJetBasis
          K hk F htransport p i) z‖ ^ 2 ≤
          (Real.sqrt A * q ^ j) ^ 2 :=
            (sq_le_sq₀ (norm_nonneg _)
              (mul_nonneg (Real.sqrt_nonneg _)
                (pow_nonneg hq j))).mpr hsection
      _ = A * (q ^ 2) ^ j := by
        rw [mul_pow, Real.sq_sqrt hA]
        congr 1
        rw [← pow_mul, ← pow_mul]
        congr 1
        omega
  have hcontract : q ^ 2 * Real.exp t ≤ 1 :=
    sourceLocalSchwarzRatio_sq_mul_exp_le_one
      dist_nonneg hR hshrink
  have hpow : (q ^ 2 * Real.exp t) ^ j ≤ 1 :=
    pow_le_one₀ (mul_nonneg (sq_nonneg q) (Real.exp_pos _).le)
      hcontract
  change
    Complex.normSq
      (momentHolomorphicRepresentative K hk F htransport
        (momentSimultaneousJetBasis
          K hk F htransport p i) z) *
      Real.exp (t * (j : ℝ)) ≤ A
  rw [Complex.normSq_eq_norm_sq,
    show t * (j : ℝ) = (j : ℝ) * t by ring,
    Real.exp_nat_mul]
  calc
    ‖momentHolomorphicRepresentative K hk F htransport
      (momentSimultaneousJetBasis
        K hk F htransport p i) z‖ ^ 2 * Real.exp t ^ j ≤
        (A * (q ^ 2) ^ j) * Real.exp t ^ j :=
          mul_le_mul_of_nonneg_right hsq
            (pow_nonneg (Real.exp_pos t).le j)
    _ = A * (q ^ 2 * Real.exp t) ^ j := by
      rw [mul_pow]
      ring
    _ ≤ A := by
      nlinarith

private theorem eventually_momentJetPartition_local_bound
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (R : ℝ) (hR : 0 < R) :
    ∀ᶠ k : ℕ in atTop, ∀ (hk : 0 < k)
      (N : ℕ) (z : TorusCharacters.LogSpace n)
      (t : ℝ), 0 ≤ t →
        dist z p < R * Real.exp (-t / 2) →
          BergmanGeodesicConvexity.exponentialPartition
            (momentHolomorphicBasisWeight K hk F htransport
              (momentSimultaneousJetBasis K hk F htransport p) z)
            (momentTruncatedJetOrder K hk F htransport p N) t ≤
              Real.exp
                ((k : ℝ) * momentLocalPotentialMaximum K F p R) *
                  sourceLocalPolynomialConstant K * (k : ℝ) ^ (3 * n) := by
  have hdim := eventually_bergmanDimension_le_volume_mul_pow K
  filter_upwards
    [eventually_momentJetBasisWeight_exp_le_local
      K F htransport p R hR, hdim]
    with k hweight hkdim hk N z t ht hshrinking
  let A : ℝ :=
    Real.exp ((k : ℝ) * momentLocalPotentialMaximum K F p R) *
      globalKernelPolynomialConstant K * (k : ℝ) ^ (2 * n)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg (Real.exp_pos _).le
        (globalKernelPolynomialConstant_pos K).le)
      (pow_nonneg (Nat.cast_nonneg k) _)
  have hsum :
      BergmanGeodesicConvexity.exponentialPartition
        (momentHolomorphicBasisWeight K hk F htransport
          (momentSimultaneousJetBasis K hk F htransport p) z)
        (momentTruncatedJetOrder K hk F htransport p N) t ≤
          (bergmanDimension K k : ℝ) * A := by
    unfold BergmanGeodesicConvexity.exponentialPartition
      BergmanGeodesicConvexity.exponentialMoment
    simp only [pow_zero, mul_one]
    calc
      (∑ i, momentHolomorphicBasisWeight K hk F htransport
          (momentSimultaneousJetBasis K hk F htransport p) z i *
            Real.exp (t *
              (momentTruncatedJetOrder
                K hk F htransport p N i : ℝ))) ≤
          ∑ _ : Fin (bergmanDimension K k), A := by
            apply Finset.sum_le_sum
            intro i _
            exact hweight hk N i z t ht hshrinking
      _ = (bergmanDimension K k : ℝ) * A := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc
    BergmanGeodesicConvexity.exponentialPartition
      (momentHolomorphicBasisWeight K hk F htransport
        (momentSimultaneousJetBasis K hk F htransport p) z)
      (momentTruncatedJetOrder K hk F htransport p N) t ≤
        (bergmanDimension K k : ℝ) * A := hsum
    _ ≤ ((normalizedVolume K.carrier + 1) *
          (k : ℝ) ^ n) * A :=
            mul_le_mul_of_nonneg_right hkdim hA
    _ = Real.exp
          ((k : ℝ) * momentLocalPotentialMaximum K F p R) *
            sourceLocalPolynomialConstant K * (k : ℝ) ^ (3 * n) := by
      dsimp [A, sourceLocalPolynomialConstant]
      rw [show 3 * n = n + 2 * n by omega, pow_add]
      ring

private theorem eventually_momentJetGeodesic_local_bound
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (R : ℝ) (hR : 0 < R) :
    ∀ᶠ k : ℕ in atTop, ∀ (hk : 0 < k)
      (N : ℕ) (z : TorusCharacters.LogSpace n)
      (t : ℝ), 0 ≤ t →
        dist z p < R * Real.exp (-t / 2) →
          momentJetGeodesic K hk F htransport p N z t ≤
            momentLocalPotentialMaximum K F p R +
              sourceLocalKernelLogError K k := by
  filter_upwards
    [eventually_momentJetPartition_local_bound
      K F htransport p R hR]
    with k hbound hk N z t ht hshrinking
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hconstant := sourceLocalPolynomialConstant_pos K
  have hpart : 0 <
      BergmanGeodesicConvexity.exponentialPartition
        (momentHolomorphicBasisWeight K hk F htransport
          (momentSimultaneousJetBasis K hk F htransport p) z)
        (momentTruncatedJetOrder K hk F htransport p N) t :=
    BergmanGeodesicConvexity.exponentialPartition_pos _ _
      (momentHolomorphicBasisWeight_nonneg K hk F htransport
        (momentSimultaneousJetBasis K hk F htransport p) z)
      (exists_positive_momentHolomorphicBasisWeight
        K hk F htransport
          (momentSimultaneousJetBasis K hk F htransport p) z) t
  have hmajor : 0 <
      Real.exp ((k : ℝ) * momentLocalPotentialMaximum K F p R) *
        sourceLocalPolynomialConstant K * (k : ℝ) ^ (3 * n) := by
    positivity
  have hlog := Real.strictMonoOn_log.monotoneOn
    hpart hmajor (hbound hk N z t ht hshrinking)
  have hexpand :
      Real.log
        (Real.exp ((k : ℝ) * momentLocalPotentialMaximum K F p R) *
          sourceLocalPolynomialConstant K * (k : ℝ) ^ (3 * n)) =
        (k : ℝ) * momentLocalPotentialMaximum K F p R +
          Real.log (sourceLocalPolynomialConstant K) +
            3 * (n : ℝ) * Real.log (k : ℝ) := by
    rw [Real.log_mul
      (mul_ne_zero (Real.exp_ne_zero _) (ne_of_gt hconstant))
        (pow_ne_zero _ (ne_of_gt hkreal)),
      Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hconstant),
      Real.log_exp, Real.log_pow]
    push_cast
    ring
  rw [hexpand] at hlog
  unfold momentJetGeodesic
    BergmanGeodesicConvexity.logarithmicPotential
    sourceLocalKernelLogError
  apply (div_le_iff₀ hkreal).mpr
  calc
    Real.log
      (BergmanGeodesicConvexity.exponentialPartition
        (momentHolomorphicBasisWeight K hk F htransport
          (momentSimultaneousJetBasis K hk F htransport p) z)
        (momentTruncatedJetOrder K hk F htransport p N) t) ≤
          (k : ℝ) * momentLocalPotentialMaximum K F p R +
            Real.log (sourceLocalPolynomialConstant K) +
              3 * (n : ℝ) * Real.log (k : ℝ) := hlog
    _ = (momentLocalPotentialMaximum K F p R +
          (Real.log (sourceLocalPolynomialConstant K) +
            3 * (n : ℝ) * Real.log (k : ℝ)) / (k : ℝ)) *
          (k : ℝ) := by
      field_simp
      ring

end BergmanJetLocalGrowth

namespace BergmanJetLocalEnvelopeGrowth

open Set Function Filter MeasureTheory Module Metric
open TorusCharacters WeightedTorusHilbert MomentOptimizer MomentFirstVariation MomentTargetGeodesic
open BergmanJetUpperEnvelope BergmanJetEnvelopeLimit BergmanJetTorusEnvelope
open BergmanJetPartitionEndpoint BergmanJetLocalGrowth ActualJetUpperEnvelope
open JetEnvelopeSlopeConvergence JetEnvelopeRightDerivative JetEnvelopeLocalGrowth
open LogPartitionConvexity
open scoped BigOperators ENNReal Topology

private theorem eventually_momentPositiveJointGeodesic_local_bound
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (R : ℝ) (hR : 0 < R) :
    ∀ᶠ k : ℕ in atTop, ∀ w ∈ sourceLocalJointRegion p R,
      momentPositiveJointGeodesic K F htransport p k w ≤
        momentLocalPotentialMaximum K F p R +
          sourceLocalKernelLogError K (k + 1) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (eventually_momentJetGeodesic_local_bound
      K F htransport p R hR)
  filter_upwards [eventually_ge_atTop N] with k hk w hw
  rw [momentPositiveJointGeodesic_eq_momentJetGeodesic]
  exact hN (k + 1) (by omega) (Nat.zero_lt_succ k)
    (Nat.floor (BodyScale.canonicalScale K *
      ((k + 1 : ℕ) : ℝ))) w.val.1 (jointLogTime w)
    (jointLogTime_pos w).le hw

private theorem eventually_momentPositiveJointGeodesic_local_le_maximum_add
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (R : ℝ) (hR : 0 < R)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ w ∈ sourceLocalJointRegion p R,
      momentPositiveJointGeodesic K F htransport p k w ≤
        momentLocalPotentialMaximum K F p R + ε := by
  have herr : ∀ᶠ k : ℕ in atTop,
      sourceLocalKernelLogError K (k + 1) < ε := by
    have htend := (tendsto_sourceLocalKernelLogError K).comp
      (Filter.tendsto_add_atTop_nat 1)
    exact htend (Iio_mem_nhds hε)
  filter_upwards
    [eventually_momentPositiveJointGeodesic_local_bound
      K F htransport p R hR, herr]
    with k hbound hsmall w hw
  exact (hbound w hw).trans (by linarith)

private theorem eventually_momentJointTailSup_local_le_maximum_add
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (R : ℝ) (hR : 0 < R)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ w ∈ sourceLocalJointRegion p R,
      momentJointTailSup K F htransport p r w ≤
        momentLocalPotentialMaximum K F p R + ε := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (eventually_momentPositiveJointGeodesic_local_le_maximum_add
      K F htransport p R hR hε)
  filter_upwards [eventually_ge_atTop N] with r hr w hw
  unfold momentJointTailSup
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨j, rfl⟩
  exact hN (momentJointTailStart K F htransport p + r + j)
    (by omega) w hw

private theorem eventually_momentJointTailUpperEnvelope_local_le_maximum_add
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (R : ℝ) (hR : 0 < R)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ w ∈ sourceLocalJointRegion p R,
      momentJointTailUpperEnvelope K F htransport p r w ≤
        momentLocalPotentialMaximum K F p R + ε := by
  filter_upwards
    [eventually_momentJointTailSup_local_le_maximum_add
      K F htransport p R hR hε]
    with r hr w hw
  unfold momentJointTailUpperEnvelope
  apply upperRegularization_le_of_eventually
  exact Filter.mem_of_superset
    ((isOpen_sourceLocalJointRegion p R).mem_nhds hw)
    (fun v hv => hr v hv)

private theorem momentJointUpperEnvelope_local_le_maximum
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (R : ℝ) (hR : 0 < R)
    (w : PositiveJointLogSpace n)
    (hw : w ∈ sourceLocalJointRegion p R) :
    momentJointUpperEnvelope K F htransport p w ≤
      momentLocalPotentialMaximum K F p R := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨r, hr⟩ :=
    (eventually_momentJointTailUpperEnvelope_local_le_maximum_add
      K F htransport p R hR hε).exists
  calc
    momentJointUpperEnvelope K F htransport p w ≤
      momentJointTailUpperEnvelope K F htransport p r w :=
        ciInf_le (momentJointTailUpperEnvelope_bddBelow
          K F htransport p w) r
    _ ≤ momentLocalPotentialMaximum K F p R + ε := hr w hw

private theorem momentEnvelopeTimeSlice_local_le_maximum
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) (R t : ℝ) (hR : 0 < R) (ht : 0 < t)
    (hz : dist z p < R * Real.exp (-t / 2)) :
    momentEnvelopeTimeSlice K F htransport p z t ≤
      momentLocalPotentialMaximum K F p R := by
  rw [momentEnvelopeTimeSlice, dite_eq_left ht]
  apply momentJointUpperEnvelope_local_le_maximum
    K F htransport p R hR
  change dist z p <
    R * Real.exp
      (-jointLogTime (sourcePositiveJointTimePoint z t ht) / 2)
  simpa only [jointLogTime_sourcePositiveJointTimePoint] using hz

private theorem momentTorusEnvelopeTimeSlice_local_le_maximum
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (q : LogTorus n)
    (R t : ℝ) (hR : 0 < R) (ht : 0 < t)
    (hq : dist (sourceTorusCoverPoint q) p <
      R * Real.exp (-t / 2)) :
    momentTorusEnvelopeTimeSlice K F htransport p q t ≤
      momentLocalPotentialMaximum K F p R := by
  exact momentEnvelopeTimeSlice_local_le_maximum
    K F htransport p (sourceTorusCoverPoint q) R t hR ht hq

private theorem momentBodyPartition_ge_local_box
    {n : ℕ} (K : CenteredBody n)
    (R t : ℝ) (hR : 0 < R) (ht : 0 < t) :
    Real.exp
        (-momentLocalPotentialMaximum K
          (momentBodyOptimizer K) (0 : LogSpace n) R) *
      sourceLocalBallVolumeConstant n R *
        Real.exp (-(n : ℝ) * t) ≤
          momentBodyPartition K (0 : LogSpace n) t := by
  let A : Set (LogTorus n) :=
    sourceLocalTorusBox n (sourceLocalBoxRadius R t)
  have hA : MeasurableSet A :=
    measurableSet_sourceLocalTorusBox n (sourceLocalBoxRadius R t)
  have hAfinite : sourceTorusBaseMeasure n A ≠ ⊤ :=
    sourceLocalTorusBox_measure_ne_top n
      (sourceLocalBoxRadius_le_one hR ht.le)
  have hconst : IntegrableOn
      (fun _ : LogTorus n =>
        Real.exp
          (-momentLocalPotentialMaximum K
            (momentBodyOptimizer K) (0 : LogSpace n) R))
      A (sourceTorusBaseMeasure n) :=
    MeasureTheory.integrableOn_const hAfinite
  have hdensity := integrable_exp_neg_momentBodyTorusWeight
    K (0 : LogSpace n) t
  have hpoint : ∀ q ∈ A,
      Real.exp
        (-momentLocalPotentialMaximum K
          (momentBodyOptimizer K) (0 : LogSpace n) R) ≤
        Real.exp (-momentBodyTorusWeight
          K (0 : LogSpace n) t q) := by
    intro q hq
    have hcover := sourceTorusCoverPoint_mem_shrinkingBall_of_mem_box
      hR q hq
    have hlocal := momentTorusEnvelopeTimeSlice_local_le_maximum
      K (momentBodyOptimizer K)
      (momentBodyOptimizer_transport K)
      (0 : LogSpace n) q R t hR ht hcover
    unfold momentBodyTorusWeight
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    Real.exp
        (-momentLocalPotentialMaximum K
          (momentBodyOptimizer K) (0 : LogSpace n) R) *
      sourceLocalBallVolumeConstant n R *
        Real.exp (-(n : ℝ) * t) =
          ∫ _q : LogTorus n in A,
            Real.exp
              (-momentLocalPotentialMaximum K
                (momentBodyOptimizer K) (0 : LogSpace n) R)
              ∂(sourceTorusBaseMeasure n) := by
            rw [MeasureTheory.setIntegral_const]
            dsimp [A]
            rw [sourceLocalTorusBox_realVolume_at_time n hR ht.le]
            ring
    _ ≤ ∫ q : LogTorus n in A,
        Real.exp (-momentBodyTorusWeight
          K (0 : LogSpace n) t q)
          ∂(sourceTorusBaseMeasure n) :=
      setIntegral_mono_on hconst hdensity.integrableOn hA hpoint
    _ ≤ ∫ q : LogTorus n,
        Real.exp (-momentBodyTorusWeight
          K (0 : LogSpace n) t q)
          ∂(sourceTorusBaseMeasure n) := by
      apply setIntegral_le_integral hdensity
      exact Filter.Eventually.of_forall fun q =>
        (Real.exp_pos
          (-momentBodyTorusWeight
            K (0 : LogSpace n) t q)).le
    _ = momentBodyPartition K (0 : LogSpace n) t := by
      rfl

private def momentBodyLocalPartitionGrowthConstant
    {n : ℕ} (K : CenteredBody n) (R : ℝ) : ℝ :=
  momentLocalPotentialMaximum K
      (momentBodyOptimizer K) (0 : LogSpace n) R -
    Real.log (sourceLocalBallVolumeConstant n R) +
    Real.log (normalizedVolume K.carrier)

private theorem momentBodyLogPartition_le_linear
    {n : ℕ} (K : CenteredBody n)
    (R t : ℝ) (hR : 0 < R) (ht : 0 < t) :
    momentBodyLogPartition K (0 : LogSpace n) t ≤
      (n : ℝ) * t + momentBodyLocalPartitionGrowthConstant K R := by
  have hconstant := sourceLocalBallVolumeConstant_pos n hR
  have hleft : 0 <
      Real.exp
        (-momentLocalPotentialMaximum K
          (momentBodyOptimizer K) (0 : LogSpace n) R) *
        sourceLocalBallVolumeConstant n R *
          Real.exp (-(n : ℝ) * t) := by
    positivity
  have hbound := momentBodyPartition_ge_local_box K R t hR ht
  have hpartition := momentBodyPartition_pos
    K (0 : LogSpace n) t
  have hlog := Real.strictMonoOn_log.monotoneOn
    hleft hpartition hbound
  rw [momentBodyLogPartition_eq_sourceLogPartition_add_log_volume]
  unfold sourceLogPartition momentBodyPartition
    momentBodyLocalPartitionGrowthConstant at *
  calc
    -Real.log
      (sourcePartition (momentBodyTorusWeight
        K (0 : LogSpace n)) t) +
          Real.log (normalizedVolume K.carrier) ≤
      -Real.log
        (Real.exp
          (-momentLocalPotentialMaximum K
            (momentBodyOptimizer K) (0 : LogSpace n) R) *
          sourceLocalBallVolumeConstant n R *
          Real.exp (-(n : ℝ) * t)) +
            Real.log (normalizedVolume K.carrier) := by
        linarith
    _ = (n : ℝ) * t +
        (momentLocalPotentialMaximum K
          (momentBodyOptimizer K) (0 : LogSpace n) R -
            Real.log (sourceLocalBallVolumeConstant n R) +
              Real.log (normalizedVolume K.carrier)) := by
      rw [Real.log_mul
        (mul_ne_zero (Real.exp_ne_zero _) hconstant.ne')
          (Real.exp_ne_zero _),
        Real.log_mul (Real.exp_ne_zero _) hconstant.ne',
        Real.log_exp, Real.log_exp]
      ring

private theorem exists_momentBodyLogPartition_linear_growth
    {n : ℕ} (K : CenteredBody n) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
      momentBodyLogPartition K (0 : LogSpace n) t ≤
        (n : ℝ) * t + C := by
  refine ⟨max (momentBodyLocalPartitionGrowthConstant K 1) 0, ?_⟩
  intro t ht
  rcases ht.eq_or_lt with rfl | ht
  · rw [momentBodyLogPartition_zero]
    simp only [mul_zero, zero_add]
    exact le_max_right _ _
  · calc
      momentBodyLogPartition K (0 : LogSpace n) t ≤
        (n : ℝ) * t + momentBodyLocalPartitionGrowthConstant K 1 :=
          momentBodyLogPartition_le_linear K 1 t (by norm_num) ht
      _ ≤ (n : ℝ) * t +
        max (momentBodyLocalPartitionGrowthConstant K 1) 0 := by
          gcongr
          exact le_max_left _ _

end BergmanJetLocalEnvelopeGrowth

namespace BergmanJetBodyLogPartitionSharpGrowth

open Set Filter
open TorusCharacters BergmanJetPartitionEndpoint
open BergmanJetJointHolomorphicUnconditionalBodyConvexity BergmanJetLocalEnvelopeGrowth
open scoped Topology

private theorem momentBodyLogPartition_le_dimension_mul
    {n : ℕ} (K : CenteredBody n)
    {t : ℝ} (ht : 0 ≤ t) :
    momentBodyLogPartition K (0 : LogSpace n) t ≤
      (n : ℝ) * t := by
  let L := momentBodyLogPartition K (0 : LogSpace n)
  have hconvex : ConvexOn ℝ (Set.Ici 0) L :=
    convexOn_momentBodyLogPartition_Ici K (0 : LogSpace n)
  have hzero : L 0 = 0 :=
    momentBodyLogPartition_zero K (0 : LogSpace n)
  obtain ⟨C, hgrowth⟩ := exists_momentBodyLogPartition_linear_growth K
  change L t ≤ (n : ℝ) * t
  rcases ht.eq_or_lt with rfl | ht'
  · simp only [hzero, mul_zero, Std.le_refl]
  apply (div_le_iff₀ ht').mp
  have hdiv : Tendsto (fun T : ℝ => C / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hlim : Tendsto (fun T : ℝ => (n : ℝ) + C / T) atTop (𝓝 n) := by
    simpa only [add_zero] using tendsto_const_nhds.add hdiv
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_gt_atTop t] with T hT
  have hT' := ht'.trans hT
  calc
    L t / t ≤ L T / T := by
      simpa only [slope_def_field, hzero, sub_zero] using
        hconvex.monotoneOn_slope_gt
          (show (0 : ℝ) ∈ Set.Ici 0 by simp only [mem_Ici, Std.le_refl])
          (show t ∈ {u ∈ Set.Ici (0 : ℝ) | 0 < u} from ⟨ht'.le, ht'⟩)
          (show T ∈ {u ∈ Set.Ici (0 : ℝ) | 0 < u} from ⟨hT'.le, hT'⟩)
          hT.le
    _ ≤ ((n : ℝ) * T + C) / T :=
      (div_le_div_iff_of_pos_right hT').mpr (hgrowth T hT'.le)
    _ = (n : ℝ) + C / T := by field_simp

end BergmanJetBodyLogPartitionSharpGrowth

namespace BergmanJetBodyExponentialSecantBridge

open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence LogPartitionConvexity
open BergmanJetPartitionEndpoint BergmanJetTorusRightSlopeGibbsBridge
open BergmanJetBodyLogPartitionSharpGrowth
open scoped BigOperators ENNReal Topology

private theorem nonnegative_le_exp_mul_one_sub_exp_neg
    {u C : ℝ} (hu : 0 ≤ u) (huC : u ≤ C) :
    u ≤ Real.exp C * (1 - Real.exp (-u)) := by
  have hexp := mul_le_mul_of_nonneg_right
    (Real.add_one_le_exp u) (Real.exp_pos (-u)).le
  have hcancel : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add]
    simp only [add_neg_cancel, Real.exp_zero]
  rw [hcancel] at hexp
  have hfactor : u * Real.exp (-u) ≤ 1 - Real.exp (-u) := by
    nlinarith
  calc
    u = u * 1 := by ring
    _ ≤ u * Real.exp (C - u) := by
      apply mul_le_mul_of_nonneg_left _ hu
      exact Real.one_le_exp (sub_nonneg.mpr huC)
    _ = Real.exp C * (u * Real.exp (-u)) := by
      rw [show C - u = C + -u by ring, Real.exp_add]
      ring
    _ ≤ Real.exp C * (1 - Real.exp (-u)) :=
      mul_le_mul_of_nonneg_left hfactor (Real.exp_pos C).le

private def momentBodyEnvelopeRelativeDensity
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) (q : LogTorus n) : ℝ :=
  Real.exp
    (-(momentBodyTorusWeight K p t q -
      momentBodyTorusWeight K p 0 q))

private theorem measurable_momentBodyEnvelopeRelativeDensity
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) :
    Measurable (momentBodyEnvelopeRelativeDensity K p t) := by
  unfold momentBodyEnvelopeRelativeDensity
  exact Real.continuous_exp.measurable.comp
    ((measurable_momentBodyTorusWeight K p t).sub
      (measurable_momentBodyTorusWeight K p 0)).neg

private theorem integral_momentBodyZeroGibbs_eq_density_integral
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (f : LogTorus n → ℝ) :
    (∫ q : LogTorus n, f q
      ∂(sourceProbability (momentBodyTorusWeight K p) 0)) =
      ∫ q : LogTorus n,
        f q * sourceNormalizedDensity
          (momentBodyTorusWeight K p) 0 q
        ∂(sourceTorusBaseMeasure n) := by
  let d : LogTorus n → ℝ≥0∞ := fun q =>
    ENNReal.ofReal
      (sourceNormalizedDensity (momentBodyTorusWeight K p) 0 q)
  have hdmeas : Measurable d := by
    apply ENNReal.measurable_ofReal.comp
    unfold sourceNormalizedDensity sourceTimeDensity
    exact ((Real.continuous_exp.measurable.comp
      (measurable_momentBodyTorusWeight K p 0).neg).div_const
        (sourcePartition (momentBodyTorusWeight K p) 0))
  have hfinite : ∀ᵐ q ∂(sourceTorusBaseMeasure n), d q < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  unfold sourceProbability
  rw [integral_withDensity_eq_integral_toReal_smul hdmeas hfinite]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with q
  rw [ENNReal.toReal_ofReal
    (sourceNormalizedDensity_momentBody_pos K p 0 q).le]
  simp only [smul_eq_mul, mul_comm]

private theorem integral_momentBodyEnvelopeRelativeDensity_eq_normalizedPartition
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) :
    (∫ q : LogTorus n,
      momentBodyEnvelopeRelativeDensity K p t q
        ∂(sourceProbability (momentBodyTorusWeight K p) 0)) =
      momentBodyNormalizedPartition K p t := by
  rw [integral_momentBodyZeroGibbs_eq_density_integral]
  unfold momentBodyEnvelopeRelativeDensity
    sourceNormalizedDensity sourceTimeDensity
    momentBodyNormalizedPartition
  change
    (∫ q : LogTorus n,
      Real.exp
        (-(momentBodyTorusWeight K p t q -
          momentBodyTorusWeight K p 0 q)) *
        (Real.exp (-momentBodyTorusWeight K p 0 q) /
          momentBodyPartition K p 0)
      ∂(sourceTorusBaseMeasure n)) =
      momentBodyPartition K p t /
        normalizedVolume K.carrier
  rw [momentBodyPartition_zero,
    momentBodyPartition_eq_integral,
    ← MeasureTheory.integral_div]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with q
  rw [← mul_div_assoc, ← Real.exp_add]
  congr 2
  ring

private theorem momentBodyEnvelopeRelativeDensity_pos
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) (q : LogTorus n) :
    0 < momentBodyEnvelopeRelativeDensity K p t q :=
  Real.exp_pos _

private theorem ae_momentBodyEnvelopeRelativeDensity_le_one
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ q : LogTorus n
      ∂(sourceProbability (momentBodyTorusWeight K p) 0),
      momentBodyEnvelopeRelativeDensity K p t q ≤ 1 := by
  filter_upwards
    [ae_momentBodyEnvelopePositiveSecant_nonneg_Gibbs
      K p ht] with q hq
  unfold momentBodyEnvelopeRelativeDensity
  rw [← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  have hmul := mul_nonneg hq ht.le
  have hid :
      momentBodyEnvelopePositiveSecant K p t q * t =
        momentBodyTorusWeight K p t q -
          momentBodyTorusWeight K p 0 q := by
    simp only [momentBodyEnvelopePositiveSecant, momentBodyTorusWeight_zero, isUnit_iff_ne_zero,
      ne_eq, ht.ne', not_false_eq_true, IsUnit.div_mul_cancel]
  linarith

private theorem integrable_momentBodyEnvelopeRelativeDensity_Gibbs
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) {t : ℝ} (ht : 0 < t) :
    Integrable (momentBodyEnvelopeRelativeDensity K p t)
      (sourceProbability (momentBodyTorusWeight K p) 0) := by
  let := sourceProbability_momentBody_isProbability K p 0
  refine (integrable_const (1 : ℝ)).mono'
    (measurable_momentBodyEnvelopeRelativeDensity
      K p t).aestronglyMeasurable ?_
  filter_upwards
    [ae_momentBodyEnvelopeRelativeDensity_le_one
      K p ht] with q hq
  rw [Real.norm_eq_abs, abs_of_pos
    (momentBodyEnvelopeRelativeDensity_pos K p t q)]
  exact hq

private theorem exp_neg_dimension_mul_le_momentBodyNormalizedPartition
    {n : ℕ} (K : CenteredBody n)
    {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-((n : ℝ) * t)) ≤
      momentBodyNormalizedPartition K (0 : LogSpace n) t := by
  have hgrowth := momentBodyLogPartition_le_dimension_mul K ht
  have hpos := momentBodyNormalizedPartition_pos
    K (0 : LogSpace n) t
  have hlog :
      -((n : ℝ) * t) ≤
        Real.log
          (momentBodyNormalizedPartition K
            (0 : LogSpace n) t) := by
    unfold momentBodyLogPartition at hgrowth
    linarith
  calc
    Real.exp (-((n : ℝ) * t)) ≤
      Real.exp
        (Real.log (momentBodyNormalizedPartition
          K (0 : LogSpace n) t)) := Real.exp_le_exp.mpr hlog
    _ = momentBodyNormalizedPartition
          K (0 : LogSpace n) t := Real.exp_log hpos

private theorem one_sub_momentBodyNormalizedPartition_le_dimension_mul
    {n : ℕ} (K : CenteredBody n)
    {t : ℝ} (ht : 0 ≤ t) :
    1 - momentBodyNormalizedPartition
      K (0 : LogSpace n) t ≤ (n : ℝ) * t := by
  have hpart :=
    exp_neg_dimension_mul_le_momentBodyNormalizedPartition K ht
  have hexp := Real.add_one_le_exp (-((n : ℝ) * t))
  linarith

private theorem integral_momentBodyEnvelopePositiveSecant_le_partition_complement
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) {t : ℝ} (ht : 0 < t) :
    (∫ q : LogTorus n,
      momentBodyEnvelopePositiveSecant K p t q
        ∂(sourceProbability (momentBodyTorusWeight K p) 0)) ≤
      Real.exp (BodyScale.canonicalScale K * t) *
        (1 - momentBodyNormalizedPartition K p t) / t := by
  let μ := sourceProbability (momentBodyTorusWeight K p) 0
  let C := BodyScale.canonicalScale K
  let := sourceProbability_momentBody_isProbability K p 0
  have hrelint :=
    integrable_momentBodyEnvelopeRelativeDensity_Gibbs K p ht
  have hrightint :
      Integrable
        (fun q : LogTorus n =>
          Real.exp (C * t) *
            (1 - momentBodyEnvelopeRelativeDensity K p t q) / t)
        μ := by
    exact
      (((integrable_const (1 : ℝ)).sub hrelint).const_mul
        (Real.exp (C * t))).div_const t
  have hpoint :
      ∀ᵐ q : LogTorus n ∂μ,
        momentBodyEnvelopePositiveSecant K p t q ≤
          Real.exp (C * t) *
            (1 - momentBodyEnvelopeRelativeDensity K p t q) / t := by
    filter_upwards
      [ae_momentBodyEnvelopePositiveSecant_nonneg_Gibbs
        K p ht] with q hq
    let u := momentBodyTorusWeight K p t q -
      momentBodyTorusWeight K p 0 q
    have hid :
        momentBodyEnvelopePositiveSecant K p t q * t = u := by
      simp only [momentBodyEnvelopePositiveSecant, momentBodyTorusWeight_zero, isUnit_iff_ne_zero,
        ne_eq, ht.ne', not_false_eq_true, IsUnit.div_mul_cancel, u]
    have hu : 0 ≤ u := by
      rw [← hid]
      exact mul_nonneg hq ht.le
    have huC : u ≤ C * t := by
      rw [← hid]
      exact mul_le_mul_of_nonneg_right
        (momentBodyEnvelopePositiveSecant_le_canonicalScale
          K p ht q) ht.le
    have hsandwich :=
      nonnegative_le_exp_mul_one_sub_exp_neg hu huC
    change
      (momentBodyTorusWeight K p t q -
        momentBodyTorusWeight K p 0 q) / t ≤
        Real.exp (C * t) *
          (1 - Real.exp
            (-(momentBodyTorusWeight K p t q -
              momentBodyTorusWeight K p 0 q))) / t
    exact (div_le_div_iff_of_pos_right ht).mpr hsandwich
  have hint := integral_mono_ae
    (integrable_momentBodyEnvelopePositiveSecant_Gibbs
      K p ht) hrightint hpoint
  have heq :
      (∫ q : LogTorus n,
        Real.exp (C * t) *
          (1 - momentBodyEnvelopeRelativeDensity K p t q) / t
        ∂μ) =
        Real.exp (C * t) *
          (1 - momentBodyNormalizedPartition K p t) / t := by
    rw [MeasureTheory.integral_div,
      MeasureTheory.integral_const_mul,
      MeasureTheory.integral_sub
        (integrable_const (1 : ℝ)) hrelint,
      integral_momentBodyEnvelopeRelativeDensity_eq_normalizedPartition]
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
  change
    (∫ q : LogTorus n,
      momentBodyEnvelopePositiveSecant K p t q ∂μ) ≤ _
  rw [← heq]
  exact hint

private theorem integral_momentBodyEnvelopePositiveSecant_le_dimension_mul_exp
    {n : ℕ} (K : CenteredBody n)
    {t : ℝ} (ht : 0 < t) :
    (∫ q : LogTorus n,
      momentBodyEnvelopePositiveSecant
        K (0 : LogSpace n) t q
        ∂(sourceProbability
          (momentBodyTorusWeight K (0 : LogSpace n)) 0)) ≤
      (n : ℝ) *
        Real.exp (BodyScale.canonicalScale K * t) := by
  have hfirst :=
    integral_momentBodyEnvelopePositiveSecant_le_partition_complement
      K (0 : LogSpace n) ht
  have hcomp :=
    one_sub_momentBodyNormalizedPartition_le_dimension_mul
      K ht.le
  have hratio :
      (1 - momentBodyNormalizedPartition
        K (0 : LogSpace n) t) / t ≤ (n : ℝ) :=
    (div_le_iff₀ ht).mpr hcomp
  calc
    (∫ q : LogTorus n,
      momentBodyEnvelopePositiveSecant
        K (0 : LogSpace n) t q
        ∂(sourceProbability
          (momentBodyTorusWeight K (0 : LogSpace n)) 0)) ≤
      Real.exp (BodyScale.canonicalScale K * t) *
        (1 - momentBodyNormalizedPartition
          K (0 : LogSpace n) t) / t := hfirst
    _ = Real.exp (BodyScale.canonicalScale K * t) *
          ((1 - momentBodyNormalizedPartition
            K (0 : LogSpace n) t) / t) := by ring
    _ ≤ Real.exp (BodyScale.canonicalScale K * t) *
          (n : ℝ) :=
      mul_le_mul_of_nonneg_left hratio
        (Real.exp_pos _).le
    _ = (n : ℝ) *
          Real.exp (BodyScale.canonicalScale K * t) := by ring

end BergmanJetBodyExponentialSecantBridge

namespace BergmanJetPortmanteauActualUpperTailBridge

open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge JetEnvelopeRightDerivative EnvelopeSpatialPeriodicity
open MomentOptimizer MomentTargetGeodesic MomentFirstVariation BergmanJetUpperEnvelope
open BergmanJetSpatialPeriodicity BergmanJetPortmanteauSlopeBridge
open scoped BigOperators ENNReal NNReal Topology

private theorem periodic_real_sourceTorusCoverPoint_projection
    {n : ℕ} (f : LogSpace n → ℝ)
    (hf : ∀ m : Fin n → ℤ,
      Function.Periodic f (imaginaryShift m))
    (z : LogSpace n) :
    f (sourceTorusCoverPoint
      (complexTorusCoverProjection n z)) = f z := by
  have hcperiod : ∀ m : Fin n → ℤ,
      Function.Periodic (fun w : LogSpace n => (f w : ℂ))
        (imaginaryShift m) := by
    intro m w
    exact congrArg (fun a : ℝ => (a : ℂ)) (hf m w)
  have hc := congrFun
    (complexTorusCoverLift_torusScalarRepresentative_eq
      (fun w : LogSpace n => (f w : ℂ)) hcperiod) z
  change
    (f (sourceTorusCoverPoint
      (complexTorusCoverProjection n z)) : ℂ) = (f z : ℂ)
    at hc
  exact congrArg Complex.re hc

private theorem upperSemicontinuous_periodic_real_torusRepresentative
    {n : ℕ} (f : LogSpace n → ℝ)
    (hfperiod : ∀ m : Fin n → ℤ,
      Function.Periodic f (imaginaryShift m))
    (hf : UpperSemicontinuous f) :
    UpperSemicontinuous
      (fun q : LogTorus n => f (sourceTorusCoverPoint q)) := by
  apply upperSemicontinuous_of_complexTorusCover
  have heq :
      (fun z : LogSpace n =>
        f (sourceTorusCoverPoint
          (complexTorusCoverProjection n z))) = f := by
    funext z
    exact periodic_real_sourceTorusCoverPoint_projection
      f hfperiod z
  rw [heq]
  exact hf

private theorem continuous_sourcePositiveJointTimePoint_fixed
    {n : ℕ} (t : ℝ) (ht : 0 < t) :
    Continuous
      (fun z : LogSpace n => sourcePositiveJointTimePoint z t ht) := by
  unfold sourcePositiveJointTimePoint
  apply Continuous.subtype_mk
  exact continuous_id.prodMk continuous_const

private theorem momentJointTailUpperEnvelope_timeSlice_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t)
    (m : Fin n → ℤ) :
    Function.Periodic
      (fun z : LogSpace n =>
        momentJointTailUpperEnvelope K F htransport p r
          (sourcePositiveJointTimePoint z t ht))
      (imaginaryShift m) := by
  intro z
  change
    momentJointTailUpperEnvelope K F htransport p r
      (sourcePositiveJointTimePoint (z + imaginaryShift m) t ht) =
    momentJointTailUpperEnvelope K F htransport p r
      (sourcePositiveJointTimePoint z t ht)
  rw [sourcePositiveJointTimePoint_spatial_translate]
  exact momentJointTailUpperEnvelope_spatial_invariant
    K F htransport p r m (sourcePositiveJointTimePoint z t ht)

private def momentTorusTailUpperEnvelopeTimeSlice
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t)
    (q : LogTorus n) : ℝ :=
  momentJointTailUpperEnvelope K F htransport p r
    (sourcePositiveJointTimePoint (sourceTorusCoverPoint q) t ht)

private theorem upperSemicontinuous_momentTorusTailUpperEnvelopeTimeSlice
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t) :
    UpperSemicontinuous
      (momentTorusTailUpperEnvelopeTimeSlice
        K F htransport p r t ht) := by
  unfold momentTorusTailUpperEnvelopeTimeSlice
  apply upperSemicontinuous_periodic_real_torusRepresentative
    (fun z : LogSpace n =>
      momentJointTailUpperEnvelope K F htransport p r
        (sourcePositiveJointTimePoint z t ht))
    (momentJointTailUpperEnvelope_timeSlice_periodic
      K F htransport p r t ht)
  exact (upperSemicontinuous_momentJointTailUpperEnvelope
    K F htransport p r).comp
      (continuous_sourcePositiveJointTimePoint_fixed t ht)

end BergmanJetPortmanteauActualUpperTailBridge

namespace BergmanJetGlobalLogKernelEquiLipschitz

open Set Function Filter MeasureTheory Metric
open SupportFunction LaplaceAsymptotics BergmanMonomials LatticeAsymptotics LaurentJetSeparatedness
open GlobalBergmanKernelBound MomentMinimizer MomentOptimizer MomentTargetGeodesic
open MomentFirstVariation MomentRegularity BergmanJetBasis MomentWeakGlobalKernel
open BergmanJetPointwiseLogKernel
open scoped BigOperators ENNReal NNReal Topology

private theorem monomial_pairing_sub_le_bodyRadius
    {n k : ℕ} (K : CenteredBody n)
    (u : monomialIndex K k)
    (x y : Space n) :
    pairing (u : Space n) x -
        pairing (u : Space n) y ≤
      ((n : ℝ) * bodyRadius K) * dist x y := by
  have hu := monomialExponent_norm_le_bodyRadius K u
  have hp := MonomialDivergence.abs_pairing_le_dimension_mul_norm
    (u : Space n) (x - y)
  calc
    pairing (u : Space n) x -
        pairing (u : Space n) y =
      pairing (u : Space n) (x - y) := by
        simp only [pairing, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    _ ≤ |pairing (u : Space n) (x - y)| :=
      le_abs_self _
    _ ≤ ((n : ℝ) * ‖(u : Space n)‖) * ‖x - y‖ := hp
    _ ≤ ((n : ℝ) * bodyRadius K) * ‖x - y‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg n))
        (norm_nonneg _)
    _ = ((n : ℝ) * bodyRadius K) * dist x y := by
      rw [dist_eq_norm]

private theorem moment_diagonalTerm_le_exp_bodyRadius_mul
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k)
    (x y : Space n) :
    diagonalTerm K k (momentNormalizedPotential F) u x ≤
      Real.exp
          ((k : ℝ) *
            (((n : ℝ) * bodyRadius K) * dist x y)) *
        diagonalTerm K k (momentNormalizedPotential F) u y := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hpair := monomial_pairing_sub_le_bodyRadius K u x y
  have hnorm := momentMonomialNormSquared_pos
    K hk F htransport u
  have hexp :
      Real.exp ((k : ℝ) * pairing (u : Space n) x) ≤
        Real.exp
          ((k : ℝ) *
            (((n : ℝ) * bodyRadius K) * dist x y)) *
          Real.exp ((k : ℝ) * pairing (u : Space n) y) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  unfold diagonalTerm
  calc
    Real.exp ((k : ℝ) * pairing (u : Space n) x) /
        monomialNormSquared k (u : Space n)
          (momentNormalizedPotential F) ≤
      (Real.exp
          ((k : ℝ) *
            (((n : ℝ) * bodyRadius K) * dist x y)) *
        Real.exp ((k : ℝ) * pairing (u : Space n) y)) /
          monomialNormSquared k (u : Space n)
            (momentNormalizedPotential F) :=
      (div_le_div_iff_of_pos_right hnorm).mpr hexp
    _ = Real.exp
          ((k : ℝ) *
            (((n : ℝ) * bodyRadius K) * dist x y)) *
        (Real.exp ((k : ℝ) * pairing (u : Space n) y) /
          monomialNormSquared k (u : Space n)
            (momentNormalizedPotential F)) := by
      ring

private theorem moment_diagonalKernel_le_exp_bodyRadius_mul
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (x y : Space n) :
    diagonalKernel K k (momentNormalizedPotential F) x ≤
      Real.exp
          ((k : ℝ) *
            (((n : ℝ) * bodyRadius K) * dist x y)) *
        diagonalKernel K k (momentNormalizedPotential F) y := by
  classical
  let := (monomialIndex_finite K hk).fintype
  unfold diagonalKernel
  rw [tsum_fintype, tsum_fintype, Finset.mul_sum]
  exact Finset.sum_le_sum fun u _ =>
    moment_diagonalTerm_le_exp_bodyRadius_mul
      K hk F htransport u x y

private theorem log_momentNormalized_diagonalKernel_div_sub_le_bodyRadius
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (x y : Space n) :
    Real.log
        (diagonalKernel K k (momentNormalizedPotential F) x) /
          (k : ℝ) -
      Real.log
        (diagonalKernel K k (momentNormalizedPotential F) y) /
          (k : ℝ) ≤
      ((n : ℝ) * bodyRadius K) * dist x y := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hx := diagonalKernel_momentNormalized_pos
    K hk F htransport x
  have hy := diagonalKernel_momentNormalized_pos
    K hk F htransport y
  have hratio := moment_diagonalKernel_le_exp_bodyRadius_mul
    K hk F htransport x y
  have hlog := Real.log_le_log hx hratio
  rw [Real.log_mul
    (Real.exp_ne_zero _) hy.ne', Real.log_exp] at hlog
  have hscaled :=
    (div_le_div_iff_of_pos_right hkreal).mpr hlog
  calc
    Real.log
        (diagonalKernel K k (momentNormalizedPotential F) x) /
          (k : ℝ) -
      Real.log
        (diagonalKernel K k (momentNormalizedPotential F) y) /
          (k : ℝ) ≤
      (((k : ℝ) *
            (((n : ℝ) * bodyRadius K) * dist x y) +
          Real.log
            (diagonalKernel K k
              (momentNormalizedPotential F) y)) /
            (k : ℝ)) -
        Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) y) /
            (k : ℝ) := by linarith
    _ = ((n : ℝ) * bodyRadius K) * dist x y := by
      (field_simp; ring)

private theorem abs_log_momentNormalized_diagonalKernel_div_sub_le_bodyRadius
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (x y : Space n) :
    |Real.log
        (diagonalKernel K k (momentNormalizedPotential F) x) /
          (k : ℝ) -
      Real.log
        (diagonalKernel K k (momentNormalizedPotential F) y) /
          (k : ℝ)| ≤
      ((n : ℝ) * bodyRadius K) * dist x y := by
  apply abs_le.mpr
  constructor
  · have h :=
      log_momentNormalized_diagonalKernel_div_sub_le_bodyRadius
        K hk F htransport y x
    rw [dist_comm y x] at h
    linarith
  · exact
      log_momentNormalized_diagonalKernel_div_sub_le_bodyRadius
        K hk F htransport x y

private theorem lipschitz_log_momentNormalized_diagonalKernel_div
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    LipschitzWith (sourceBodyLipschitzConstant K)
      (fun x : Space n =>
        Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) x) / (k : ℝ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h :=
    abs_log_momentNormalized_diagonalKernel_div_sub_le_bodyRadius
      K hk F htransport x y
  have hnonneg : 0 ≤ (n : ℝ) * bodyRadius K :=
    mul_nonneg (Nat.cast_nonneg n) (bodyRadius_pos K).le
  simpa only [Real.dist_eq, sourceBodyLipschitzConstant, Real.coe_toNNReal _ hnonneg,
    ge_iff_le] using h

private theorem dense_finiteEnergySourceInteriorDifferentiability
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    Dense
      {x : Space n |
        DifferentiableAt ℝ
            (F.potential : Space n → ℝ) x ∧
          SpatialBergmanFatouScheffe.actualGradient
            F.potential x ∈ interior K.carrier} := by
  apply MeasureTheory.Measure.dense_of_ae
    (μ := (volume : Measure (Space n)))
  exact (ae_differentiableAt_finiteEnergySource F).and
    (ae_finiteEnergySourceGradient_mem_interior_volume F htransport)

/-- Equi-Lipschitz functions converging on a dense set converge everywhere. -/
public
theorem tendsto_of_dense_eventually_equiLipschitz
    {X : Type*} [PseudoMetricSpace X]
    (f : ℕ → X → ℝ) (g : X → ℝ)
    (C : ℝ≥0)
    (hf : ∀ᶠ k : ℕ in atTop, LipschitzWith C (f k))
    (hg : LipschitzWith C g)
    {S : Set X} (hS : Dense S)
    (hconv : ∀ y ∈ S,
      Tendsto (fun k : ℕ => f k y) atTop (𝓝 (g y)))
    (x : X) :
    Tendsto (fun k : ℕ => f k x) atTop (𝓝 (g x)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ : ℝ := ε / (4 * ((C : ℝ) + 1))
  have hC : 0 ≤ (C : ℝ) := C.coe_nonneg
  have hC1 : 0 < (C : ℝ) + 1 := by linarith
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨y, hy, hxy⟩ := hS.exists_dist_lt x hδ
  have hsmall : (C : ℝ) * dist x y < ε / 4 := by
    calc
      (C : ℝ) * dist x y ≤
          ((C : ℝ) + 1) * dist x y := by
        exact mul_le_mul_of_nonneg_right (by linarith)
          (dist_nonneg : 0 ≤ dist x y)
      _ < ((C : ℝ) + 1) * δ :=
        mul_lt_mul_of_pos_left hxy hC1
      _ = ε / 4 := by
        dsimp [δ]
        field_simp [hC1.ne']
  have hmiddle :
      ∀ᶠ k : ℕ in atTop, dist (f k y) (g y) < ε / 2 := by
    have h := (hconv y hy)
      (Metric.ball_mem_nhds (g y) (half_pos hε))
    change
      ∀ᶠ k : ℕ in atTop, f k y ∈ Metric.ball (g y) (ε / 2)
      at h
    filter_upwards [h] with k hk
    exact Metric.mem_ball.mp hk
  have hnear :
      ∀ᶠ k : ℕ in atTop, dist (f k x) (g x) < ε := by
    filter_upwards [hf, hmiddle] with k hfk hmid
    have hfirst := hfk.dist_le_mul x y
    have hlast : dist (g y) (g x) ≤
        (C : ℝ) * dist x y := by
      calc
        dist (g y) (g x) = dist (g x) (g y) := dist_comm _ _
        _ ≤ (C : ℝ) * dist x y := hg.dist_le_mul x y
    calc
      dist (f k x) (g x) ≤
          dist (f k x) (f k y) + dist (f k y) (g x) :=
        dist_triangle _ _ _
      _ ≤ dist (f k x) (f k y) +
          (dist (f k y) (g y) + dist (g y) (g x)) :=
        by
          simpa only [add_le_add_iff_left, add_comm] using
            (add_le_add_left
              (dist_triangle (f k y) (g y) (g x))
              (dist (f k x) (f k y)))
      _ < ε := by linarith
  exact Filter.eventually_atTop.mp hnear

private theorem finiteEnergySourceNormalized_actualGradient_phase_max
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x)
    (z : Space n) :
    phase
        (SpatialBergmanFatouScheffe.actualGradient
          F.potential x)
        (momentNormalizedPotential F) z ≤
      phase
        (SpatialBergmanFatouScheffe.actualGradient
          F.potential x)
        (momentNormalizedPotential F) x := by
  have h := finiteEnergySourcePhase_actualGradient_le F x hx z
  unfold phase at h ⊢
  simp only [momentNormalizedPotential]
  linarith

private theorem tendsto_log_momentNormalized_diagonalKernel_div_all
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (x : Space n) :
    Tendsto
      (fun k : ℕ =>
        Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) x) / (k : ℝ))
      atTop (𝓝 (momentNormalizedPotential F x)) := by
  let f : ℕ → Space n → ℝ :=
    fun k y =>
      Real.log
        (diagonalKernel K k
          (momentNormalizedPotential F) y) / (k : ℝ)
  let S : Set (Space n) :=
    {y : Space n |
      DifferentiableAt ℝ
          (F.potential : Space n → ℝ) y ∧
        SpatialBergmanFatouScheffe.actualGradient
          F.potential y ∈ interior K.carrier}
  have hf : ∀ᶠ k : ℕ in atTop,
      LipschitzWith (sourceBodyLipschitzConstant K) (f k) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
    exact lipschitz_log_momentNormalized_diagonalKernel_div
      K hk F htransport
  have hS : Dense S :=
    dense_finiteEnergySourceInteriorDifferentiability
      K F htransport
  have hconv : ∀ y ∈ S,
      Tendsto (fun k : ℕ => f k y)
        atTop (𝓝 (momentNormalizedPotential F y)) := by
    intro y hy
    exact tendsto_log_momentNormalized_diagonalKernel_div
      K F htransport hy.2 y
      (finiteEnergySourceNormalized_actualGradient_phase_max
        F y hy.1)
  exact tendsto_of_dense_eventually_equiLipschitz
    f (momentNormalizedPotential F)
    (sourceBodyLipschitzConstant K) hf
    (lipschitz_momentNormalizedPotential F)
    hS hconv x

private theorem exists_open_eventual_uniform_of_equiLipschitz
    {X : Type*} [PseudoMetricSpace X]
    (f : ℕ → X → ℝ) (g : X → ℝ)
    (C : ℝ≥0)
    (hf : ∀ᶠ k : ℕ in atTop, LipschitzWith C (f k))
    (hg : LipschitzWith C g)
    (x : X)
    (hx : Tendsto (fun k : ℕ => f k x) atTop (𝓝 (g x)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ᶠ k : ℕ in atTop, ∀ y ∈ U,
        dist (f k y) (g y) < ε := by
  let δ : ℝ := ε / (4 * ((C : ℝ) + 1))
  have hC : 0 ≤ (C : ℝ) := C.coe_nonneg
  have hC1 : 0 < (C : ℝ) + 1 := by linarith
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hmiddle :
      ∀ᶠ k : ℕ in atTop, dist (f k x) (g x) < ε / 2 := by
    have h := hx (Metric.ball_mem_nhds (g x) (half_pos hε))
    change
      ∀ᶠ k : ℕ in atTop, f k x ∈ Metric.ball (g x) (ε / 2)
      at h
    filter_upwards [h] with k hk
    exact Metric.mem_ball.mp hk
  refine ⟨Metric.ball x δ, Metric.isOpen_ball,
    Metric.mem_ball_self hδ, ?_⟩
  filter_upwards [hf, hmiddle] with k hfk hmid y hy
  have hyball : dist y x < δ := Metric.mem_ball.mp hy
  have hxy : dist x y < δ := by
    simpa only [dist_comm] using hyball
  have hsmall : (C : ℝ) * dist x y < ε / 4 := by
    calc
      (C : ℝ) * dist x y ≤
          ((C : ℝ) + 1) * dist x y := by
        exact mul_le_mul_of_nonneg_right (by linarith)
          (dist_nonneg : 0 ≤ dist x y)
      _ < ((C : ℝ) + 1) * δ :=
        mul_lt_mul_of_pos_left hxy hC1
      _ = ε / 4 := by
        dsimp [δ]
        field_simp [hC1.ne']
  have hfirst : dist (f k y) (f k x) ≤
      (C : ℝ) * dist x y := by
    calc
      dist (f k y) (f k x) = dist (f k x) (f k y) :=
        dist_comm _ _
      _ ≤ (C : ℝ) * dist x y := hfk.dist_le_mul x y
  have hlast : dist (g x) (g y) ≤
      (C : ℝ) * dist x y := hg.dist_le_mul x y
  calc
    dist (f k y) (g y) ≤
        dist (f k y) (f k x) + dist (f k x) (g y) :=
      dist_triangle _ _ _
    _ ≤ dist (f k y) (f k x) +
        (dist (f k x) (g x) + dist (g x) (g y)) :=
      by
        simpa only [add_comm] using
          (add_le_add_left
            (dist_triangle (f k x) (g x) (g y))
            (dist (f k y) (f k x)))
    _ < ε := by linarith

private theorem exists_open_eventual_log_momentNormalized_diagonalKernel_uniform_all
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (x : Space n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set (Space n),
      IsOpen U ∧ x ∈ U ∧
        ∀ᶠ k : ℕ in atTop, ∀ y ∈ U,
          dist
            (Real.log
              (diagonalKernel K k
                (momentNormalizedPotential F) y) /
                  (k : ℝ))
            (momentNormalizedPotential F y) < ε := by
  let f : ℕ → Space n → ℝ :=
    fun k y =>
      Real.log
        (diagonalKernel K k
          (momentNormalizedPotential F) y) / (k : ℝ)
  have hf : ∀ᶠ k : ℕ in atTop,
      LipschitzWith (sourceBodyLipschitzConstant K) (f k) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
    exact lipschitz_log_momentNormalized_diagonalKernel_div
      K hk F htransport
  exact exists_open_eventual_uniform_of_equiLipschitz
    f (momentNormalizedPotential F)
    (sourceBodyLipschitzConstant K) hf
    (lipschitz_momentNormalizedPotential F) x
    (tendsto_log_momentNormalized_diagonalKernel_div_all
      K F htransport x) hε

private theorem exists_open_eventual_log_momentNormalized_diagonalKernel_div_ge_sub_all
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (x : Space n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set (Space n),
      IsOpen U ∧ x ∈ U ∧
        ∀ᶠ k : ℕ in atTop, ∀ y ∈ U,
          momentNormalizedPotential F y - ε ≤
            Real.log
              (diagonalKernel K k
                (momentNormalizedPotential F) y) /
                  (k : ℝ) := by
  obtain ⟨U, hU, hx, huniform⟩ :=
    exists_open_eventual_log_momentNormalized_diagonalKernel_uniform_all
      K F htransport x hε
  refine ⟨U, hU, hx, ?_⟩
  filter_upwards [huniform] with k hk y hy
  have h := hk y hy
  rw [Real.dist_eq] at h
  have habs := (abs_lt.mp h).1
  linarith

end BergmanJetGlobalLogKernelEquiLipschitz

namespace BergmanJetTorusSlopeJointNeighborhoodUpper

open Set Function Filter MeasureTheory Metric
open TorusCharacters WeightedTorusHilbert BergmanMonomials JetEnvelopeRightDerivative
open MomentOptimizer MomentTargetGeodesic MomentFirstVariation MomentRegularity MomentWeakBergman
open BergmanJetRealGeodesic BergmanJetUpperEnvelope BergmanJetTorusSlopeBridge
open BergmanJetTorusRightSlopeBridge BergmanJetGlobalLogKernelEquiLipschitz
open BergmanJetPortmanteauActualUpperTailBridge
open scoped BigOperators ENNReal NNReal Topology

private def momentTorusTailPositiveSecant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t)
    (q : LogTorus n) : ℝ :=
  (momentTorusTailUpperEnvelopeTimeSlice
      K F htransport p r t ht q -
    momentNormalizedPotential F q.1) / t

private def momentTorusClampedTailPositiveSecant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t)
    (q : LogTorus n) : ℝ :=
  max 0 (momentTorusTailPositiveSecant
    K F htransport p r t ht q)

private theorem upperSemicontinuous_momentTorusTailPositiveSecant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t) :
    UpperSemicontinuous
      (momentTorusTailPositiveSecant
        K F htransport p r t ht) := by
  have htail :=
    upperSemicontinuous_momentTorusTailUpperEnvelopeTimeSlice
      K F htransport p r t ht
  have hpot : Continuous
      (fun q : LogTorus n =>
        -momentNormalizedPotential F q.1) :=
    ((continuous_momentNormalizedPotential F).comp
      continuous_fst).neg
  have hsub : UpperSemicontinuous
      (fun q : LogTorus n =>
        momentTorusTailUpperEnvelopeTimeSlice
            K F htransport p r t ht q +
          -momentNormalizedPotential F q.1) :=
    htail.add hpot.upperSemicontinuous
  have hscale : Continuous (fun x : ℝ => x / t) :=
    continuous_id.div_const t
  have hmono : Monotone (fun x : ℝ => x / t) := by
    intro a b hab
    exact (div_le_div_iff_of_pos_right ht).mpr hab
  have h := hscale.comp_upperSemicontinuous hsub hmono
  have hsecant :
      ((fun x : ℝ => x / t) ∘
        (fun q : LogTorus n =>
          momentTorusTailUpperEnvelopeTimeSlice
              K F htransport p r t ht q +
            -momentNormalizedPotential F q.1)) =
        momentTorusTailPositiveSecant
          K F htransport p r t ht := by
    funext q
    dsimp [momentTorusTailPositiveSecant, Function.comp_def]
    ring
  rw [hsecant] at h
  exact h

private theorem upperSemicontinuous_momentTorusClampedTailPositiveSecant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t) :
    UpperSemicontinuous
      (momentTorusClampedTailPositiveSecant
        K F htransport p r t ht) := by
  have h : UpperSemicontinuous
      (fun q : LogTorus n =>
        max (0 : ℝ)
          (momentTorusTailPositiveSecant
            K F htransport p r t ht q)) :=
    upperSemicontinuous_const.sup
      (upperSemicontinuous_momentTorusTailPositiveSecant
        K F htransport p r t ht)
  have hclamp :
      (fun q : LogTorus n =>
        max (0 : ℝ)
          (momentTorusTailPositiveSecant
            K F htransport p r t ht q)) =
        momentTorusClampedTailPositiveSecant
          K F htransport p r t ht := by
    funext q
    rfl
  rw [hclamp] at h
  exact h

private theorem momentTorusJetSlope_le_tail_zeroTimeSecant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r k : ℕ)
    (hk : momentJointTailStart K F htransport p + r + 1 ≤ k)
    (q : LogTorus n) (t : ℝ) (ht : 0 < t) :
    momentTorusJetSlope K F htransport p k q ≤
      (momentTorusTailUpperEnvelopeTimeSlice
          K F htransport p r t ht q -
        Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) q.1) /
              (k : ℝ)) / t := by
  have hkpos : 0 < k := by omega
  have htail :
      momentJointTailStart K F htransport p + r ≤ k - 1 := by
    omega
  have hkadd : k - 1 + 1 = k := by omega
  let z := sourceTorusCoverPoint q
  let N := Nat.floor
    (BodyScale.canonicalScale K * (k : ℝ))
  let B := momentTorusTailUpperEnvelopeTimeSlice
    K F htransport p r t ht q
  have htime :
      momentJetGeodesic K hkpos F htransport p N z t ≤ B := by
    have hfinite :=
      momentPositiveJointGeodesic_le_tailUpperEnvelope
        K F htransport p r (k - 1) htail
          (sourcePositiveJointTimePoint z t ht)
    rw [momentPositiveJointGeodesic_eq_momentJetGeodesic,
      jointLogTime_sourcePositiveJointTimePoint] at hfinite
    simpa [hkadd, N, B, z,
      momentTorusTailUpperEnvelopeTimeSlice,
      sourcePositiveJointTimePoint] using hfinite
  have hzeroeq :
      momentJetGeodesic K hkpos F htransport p N z 0 =
        Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) q.1) / (k : ℝ) := by
    rw [momentJetGeodesic_zero_eq_log_diagonalKernel]
    exact congrArg
      (fun x : Space n =>
        Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) x) / (k : ℝ))
      (realLogCoordinate_sourceTorusCoverPoint q)
  have hfiniteSlope :=
    momentPositiveTorusJetSlope_le_cover_positive_secant
      K hkpos F htransport p N q ht
  change momentTorusJetSlope K F htransport p k q ≤
    (B - Real.log
      (diagonalKernel K k
        (momentNormalizedPotential F) q.1) / (k : ℝ)) / t
  simp only [momentTorusJetSlope, dite_eq_left hkpos]
  change momentPositiveTorusJetSlope
    K hkpos F htransport p N q ≤ _
  calc
    momentPositiveTorusJetSlope
        K hkpos F htransport p N q ≤
      (momentJetGeodesic K hkpos F htransport p N z t -
        momentJetGeodesic K hkpos F htransport p N z 0) / t :=
      hfiniteSlope
    _ ≤ (B - Real.log
        (diagonalKernel K k
          (momentNormalizedPotential F) q.1) / (k : ℝ)) / t := by
      rw [hzeroeq]
      exact (div_le_div_iff_of_pos_right ht).mpr
        (sub_le_sub_right htime _)

private theorem eventual_open_momentTorusJetSlope_lt_clampedTailSecant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t)
    (q : LogTorus n) (a : ℝ)
    (ha : momentTorusClampedTailPositiveSecant
      K F htransport p r t ht q < a) :
    ∃ (N : ℕ) (U : Set (LogTorus n)),
      IsOpen U ∧ q ∈ U ∧
        ∀ (k : ℕ), N ≤ k → ∀ y ∈ U,
          momentTorusJetSlope K F htransport p k y < a := by
  let G : LogTorus n → ℝ :=
    momentTorusClampedTailPositiveSecant
      K F htransport p r t ht
  let η : ℝ := (a - G q) / 2
  have hη : 0 < η := by
    dsimp [η, G]
    linarith
  have hηt : 0 < η * t := mul_pos hη ht
  obtain ⟨V, hV, hqV, hzero⟩ :=
    exists_open_eventual_log_momentNormalized_diagonalKernel_div_ge_sub_all
      K F htransport q.1 hηt
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hzero
  have hG : UpperSemicontinuous G :=
    upperSemicontinuous_momentTorusClampedTailPositiveSecant
      K F htransport p r t ht
  let W : Set (LogTorus n) :=
    {y : LogTorus n | G y < G q + η} ∩
      ((fun y : LogTorus n => y.1) ⁻¹' V)
  have hW : IsOpen W := by
    exact (hG.isOpen_preimage (G q + η)).inter
      (hV.preimage continuous_fst)
  have hqW : q ∈ W := by
    refine ⟨?_, hqV⟩
    change G q < G q + η
    linarith
  refine ⟨max N₀
    (momentJointTailStart K F htransport p + r + 1),
      W, hW, hqW, ?_⟩
  intro k hk y hy
  have hk₀ : N₀ ≤ k :=
    le_trans (le_max_left _ _) hk
  have hktail :
      momentJointTailStart K F htransport p + r + 1 ≤ k :=
    le_trans (le_max_right _ _) hk
  have hlog := hN₀ k hk₀ y.1 hy.2
  have hfinite := momentTorusJetSlope_le_tail_zeroTimeSecant
    K F htransport p r k hktail y t ht
  have hsec :
      momentTorusTailPositiveSecant
        K F htransport p r t ht y ≤ G y :=
    le_max_right _ _
  have hquot :
      (momentTorusTailUpperEnvelopeTimeSlice
          K F htransport p r t ht y -
        Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) y.1) /
              (k : ℝ)) / t ≤
      momentTorusTailPositiveSecant
          K F htransport p r t ht y + η := by
    unfold momentTorusTailPositiveSecant
    apply (div_le_iff₀ ht).mpr
    have hlog' := hlog
    field_simp [ht.ne']
    linarith
  have hyG : G y < G q + η := hy.1
  calc
    momentTorusJetSlope K F htransport p k y ≤
      (momentTorusTailUpperEnvelopeTimeSlice
          K F htransport p r t ht y -
        Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) y.1) /
              (k : ℝ)) / t := hfinite
    _ ≤ momentTorusTailPositiveSecant
        K F htransport p r t ht y + η := hquot
    _ ≤ G y + η := by linarith
    _ < a := by
      dsimp [η] at hyG ⊢
      linarith

end BergmanJetTorusSlopeJointNeighborhoodUpper

namespace BergmanJetPortmanteauActualVolumeBridge

open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert JetEnvelopeRightDerivative LogPartitionConvexity
open MomentRegularity BergmanJetUpperEnvelope BergmanJetEnvelopeLimit BergmanJetTorusEnvelope
open BergmanJetPartitionEndpoint BergmanJetTorusSlopeBridge BergmanJetTorusRightSlopeBridge
open BergmanJetTorusRightSlopeGibbsBridge BergmanJetBodyExponentialSecantBridge
open BergmanJetPortmanteauMovingUpperTailBridge BergmanJetPortmanteauActualUpperTailBridge
open BergmanJetTorusSlopeJointNeighborhoodUpper
open scoped BigOperators ENNReal NNReal Topology

private def momentBodyMovingBergmanProbability
    {n : ℕ} (K : CenteredBody n) (k : ℕ) :
    ProbabilityMeasure (LogTorus n) :=
  ⟨momentTorusBergmanProbability
      K (momentBodyOptimizer K) (k + 1),
    momentTorusBergmanProbability_isProbability
      K (Nat.zero_lt_succ k) (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K)⟩

private def momentBodyZeroGibbsProbability
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) : ProbabilityMeasure (LogTorus n) :=
  ⟨sourceProbability (momentBodyTorusWeight K p) 0,
    sourceProbability_momentBody_isProbability K p 0⟩

private def momentBodyTailPositiveSecant
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t)
    (q : LogTorus n) : ℝ :=
  (momentTorusTailUpperEnvelopeTimeSlice
      K (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K) p r t ht q -
    momentNormalizedPotential (momentBodyOptimizer K) q.1) / t

private def momentBodyClampedTailPositiveSecant
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t)
    (q : LogTorus n) : ℝ :=
  max 0 (momentBodyTailPositiveSecant K p r t ht q)

private theorem upperSemicontinuous_momentBodyTailPositiveSecant
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t) :
    UpperSemicontinuous
      (momentBodyTailPositiveSecant K p r t ht) := by
  have h := upperSemicontinuous_momentTorusTailPositiveSecant
    K (momentBodyOptimizer K)
      (momentBodyOptimizer_transport K) p r t ht
  have hsecant :
      momentTorusTailPositiveSecant
          K (momentBodyOptimizer K)
          (momentBodyOptimizer_transport K) p r t ht =
        momentBodyTailPositiveSecant K p r t ht := by
    funext q
    rfl
  rw [hsecant] at h
  exact h

private theorem upperSemicontinuous_momentBodyClampedTailPositiveSecant
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t) :
    UpperSemicontinuous
      (momentBodyClampedTailPositiveSecant K p r t ht) := by
  unfold momentBodyClampedTailPositiveSecant
  exact (continuous_const.upperSemicontinuous).sup
    (upperSemicontinuous_momentBodyTailPositiveSecant
      K p r t ht)

private theorem momentBodyTailPositiveSecant_le_scale_add_inv
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t)
    (q : LogTorus n) :
    momentBodyTailPositiveSecant K p r t ht q ≤
      BodyScale.canonicalScale K + 1 / t := by
  have hmajor := momentJointTailUpperEnvelope_le_majorant_add_one
    K (momentBodyOptimizer K)
      (momentBodyOptimizer_transport K) p r
        (sourcePositiveJointTimePoint (sourceTorusCoverPoint q) t ht)
  have hmajor' :
      momentTorusTailUpperEnvelopeTimeSlice
          K (momentBodyOptimizer K)
            (momentBodyOptimizer_transport K) p r t ht q ≤
        momentNormalizedPotential
            (momentBodyOptimizer K) q.1 +
          BodyScale.canonicalScale K * t + 1 := by
    simpa only [momentTorusTailUpperEnvelopeTimeSlice, momentJointMajorant,
      jointRealCoordinate_sourcePositiveJointTimePoint, realLogCoordinate_sourceTorusCoverPoint,
      jointLogTime_sourcePositiveJointTimePoint] using hmajor
  unfold momentBodyTailPositiveSecant
  calc
    (momentTorusTailUpperEnvelopeTimeSlice
          K (momentBodyOptimizer K)
            (momentBodyOptimizer_transport K) p r t ht q -
        momentNormalizedPotential
          (momentBodyOptimizer K) q.1) / t ≤
      (BodyScale.canonicalScale K * t + 1) / t :=
        (div_le_div_iff_of_pos_right ht).mpr (by linarith)
    _ = BodyScale.canonicalScale K + 1 / t := by
      field_simp

private theorem momentBodyClampedTailPositiveSecant_nonneg
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t)
    (q : LogTorus n) :
    0 ≤ momentBodyClampedTailPositiveSecant K p r t ht q :=
  le_max_left _ _

private theorem momentBodyClampedTailPositiveSecant_le_scale_add_inv
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t)
    (q : LogTorus n) :
    momentBodyClampedTailPositiveSecant K p r t ht q ≤
      BodyScale.canonicalScale K + 1 / t := by
  unfold momentBodyClampedTailPositiveSecant
  apply max_le
  · exact add_nonneg (BodyScale.canonicalScale_pos K).le
      (by positivity)
  · exact momentBodyTailPositiveSecant_le_scale_add_inv
      K p r t ht q

private theorem limsup_momentBodyMovingJetIntegral_le_clampedTail
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t)
    (hweak : Tendsto (momentBodyMovingBergmanProbability K) atTop
      (𝓝 (momentBodyZeroGibbsProbability K p)))
    (hupper : ∀ (q : LogTorus n) (a : ℝ),
      momentBodyClampedTailPositiveSecant K p r t ht q < a →
        ∃ (N : ℕ) (U : Set (LogTorus n)), IsOpen U ∧ q ∈ U ∧
          ∀ k : ℕ, N ≤ k → ∀ y ∈ U,
            momentTorusJetSlope
              K (momentBodyOptimizer K)
                (momentBodyOptimizer_transport K) p (k + 1) y < a) :
    Filter.limsup
        (fun k : ℕ =>
          ∫ q : LogTorus n,
            momentTorusJetSlope
              K (momentBodyOptimizer K)
                (momentBodyOptimizer_transport K) p (k + 1) q
              ∂(momentTorusBergmanProbability
                K (momentBodyOptimizer K) (k + 1))) atTop ≤
      ∫ q : LogTorus n,
        momentBodyClampedTailPositiveSecant K p r t ht q
          ∂(sourceProbability (momentBodyTorusWeight K p) 0) := by
  let C : ℝ := BodyScale.canonicalScale K + 1 / t
  have hC : 0 ≤ C := add_nonneg
    (BodyScale.canonicalScale_pos K).le (by positivity)
  have hscale : BodyScale.canonicalScale K ≤ C := by
    dsimp [C]
    linarith [show 0 ≤ (1 / t : ℝ) by positivity]
  exact limsup_integral_moving_le_of_probability_tendsto_and_eventual_open_upper
    (momentBodyZeroGibbsProbability K p)
    (momentBodyMovingBergmanProbability K)
    hweak
    (fun k : ℕ =>
      momentTorusJetSlope K (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K) p (k + 1))
    (momentBodyClampedTailPositiveSecant K p r t ht)
    C
    (fun k =>
      (continuous_momentTorusJetSlope
        K (momentBodyOptimizer K)
          (momentBodyOptimizer_transport K) p (k + 1)).measurable)
    (upperSemicontinuous_momentBodyClampedTailPositiveSecant
      K p r t ht)
    hC
    (fun k q => momentTorusJetSlope_nonneg
      K (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K) p (k + 1) q)
    (fun k q => (momentTorusJetSlope_le_canonicalScale
      K (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K) p (k + 1) q).trans
          hscale)
    (momentBodyClampedTailPositiveSecant_nonneg K p r t ht)
    (momentBodyClampedTailPositiveSecant_le_scale_add_inv
      K p r t ht)
    hupper

private theorem momentBodyJetSlopeEventualOpenTailUpper_unconditional
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t) :
    ∀ (q : LogTorus n) (a : ℝ),
      momentBodyClampedTailPositiveSecant K p r t ht q < a →
        ∃ (N : ℕ) (U : Set (LogTorus n)), IsOpen U ∧ q ∈ U ∧
          ∀ k : ℕ, N ≤ k → ∀ y ∈ U,
            momentTorusJetSlope
              K (momentBodyOptimizer K)
                (momentBodyOptimizer_transport K) p (k + 1) y < a := by
  intro q a ha
  have ha' :
      momentTorusClampedTailPositiveSecant
        K (momentBodyOptimizer K)
          (momentBodyOptimizer_transport K) p r t ht q < a := by
    simpa only [momentTorusClampedTailPositiveSecant, momentTorusTailPositiveSecant, sup_lt_iff,
      momentBodyClampedTailPositiveSecant, momentBodyTailPositiveSecant] using ha
  obtain ⟨N, U, hU, hq, hfinite⟩ :=
    eventual_open_momentTorusJetSlope_lt_clampedTailSecant
      K (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K)
        p r t ht q a ha'
  refine ⟨N, U, hU, hq, ?_⟩
  intro k hk y hy
  exact hfinite (k + 1) (by omega) y hy

private theorem limsup_momentBodyMovingJetIntegral_le_clampedTail_of_weak
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t)
    (hweak : Tendsto (momentBodyMovingBergmanProbability K) atTop
      (𝓝 (momentBodyZeroGibbsProbability K p))) :
    Filter.limsup
        (fun k : ℕ =>
          ∫ q : LogTorus n,
            momentTorusJetSlope
              K (momentBodyOptimizer K)
                (momentBodyOptimizer_transport K) p (k + 1) q
              ∂(momentTorusBergmanProbability
                K (momentBodyOptimizer K) (k + 1))) atTop ≤
      ∫ q : LogTorus n,
        momentBodyClampedTailPositiveSecant K p r t ht q
          ∂(sourceProbability (momentBodyTorusWeight K p) 0) :=
  limsup_momentBodyMovingJetIntegral_le_clampedTail
    K p r t ht hweak
      (momentBodyJetSlopeEventualOpenTailUpper_unconditional
        K p r t ht)

private theorem tendsto_momentBodyTailPositiveSecant
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) (ht : 0 < t)
    (q : LogTorus n) :
    Tendsto
      (fun r : ℕ => momentBodyTailPositiveSecant K p r t ht q)
      atTop
      (𝓝 (momentBodyEnvelopePositiveSecant K p t q)) := by
  have htail :=
    tendsto_momentJointTailUpperEnvelope
      K (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K) p
          (sourcePositiveJointTimePoint (sourceTorusCoverPoint q) t ht)
  have hsec :=
    (htail.sub (tendsto_const_nhds
      (x := momentNormalizedPotential
        (momentBodyOptimizer K) q.1))).div_const t
  simpa only [momentBodyTailPositiveSecant, momentTorusTailUpperEnvelopeTimeSlice,
    momentBodyEnvelopePositiveSecant, momentBodyTorusWeight, momentTorusEnvelopeTimeSlice,
    momentEnvelopeTimeSlice, ht, ↓reduceDIte, lt_self_iff_false,
    realLogCoordinate_sourceTorusCoverPoint] using hsec

private theorem tendsto_momentBodyClampedTailPositiveSecant
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) (ht : 0 < t)
    (q : LogTorus n) :
    Tendsto
      (fun r : ℕ =>
        momentBodyClampedTailPositiveSecant K p r t ht q)
      atTop
      (𝓝 (max 0 (momentBodyEnvelopePositiveSecant K p t q))) := by
  simpa only [momentBodyClampedTailPositiveSecant] using
    (tendsto_const_nhds (x := (0 : ℝ))).max
      (tendsto_momentBodyTailPositiveSecant K p t ht q)

private theorem tendsto_integral_momentBodyClampedTailPositiveSecant
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) (ht : 0 < t) :
    Tendsto
      (fun r : ℕ =>
        ∫ q : LogTorus n,
          momentBodyClampedTailPositiveSecant K p r t ht q
            ∂(sourceProbability (momentBodyTorusWeight K p) 0))
      atTop
      (𝓝 (∫ q : LogTorus n,
        momentBodyEnvelopePositiveSecant K p t q
          ∂(sourceProbability (momentBodyTorusWeight K p) 0))) := by
  let μ : Measure (LogTorus n) :=
    sourceProbability (momentBodyTorusWeight K p) 0
  let : IsProbabilityMeasure μ :=
    sourceProbability_momentBody_isProbability K p 0
  have hlim :
      Tendsto
        (fun r : ℕ =>
          ∫ q : LogTorus n,
            momentBodyClampedTailPositiveSecant K p r t ht q ∂μ)
        atTop
        (𝓝 (∫ q : LogTorus n,
          max 0 (momentBodyEnvelopePositiveSecant K p t q) ∂μ)) := by
    apply MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : LogTorus n => BodyScale.canonicalScale K + 1 / t)
    · intro r
      exact
        (upperSemicontinuous_momentBodyClampedTailPositiveSecant
          K p r t ht).measurable.aestronglyMeasurable
    · exact integrable_const _
    · intro r
      exact Filter.Eventually.of_forall fun q => by
        rw [Real.norm_eq_abs,
          abs_of_nonneg
            (momentBodyClampedTailPositiveSecant_nonneg
              K p r t ht q)]
        exact momentBodyClampedTailPositiveSecant_le_scale_add_inv
          K p r t ht q
    · exact Filter.Eventually.of_forall
        (tendsto_momentBodyClampedTailPositiveSecant K p t ht)
  have hEq :
      (∫ q : LogTorus n,
        max 0 (momentBodyEnvelopePositiveSecant K p t q) ∂μ) =
        ∫ q : LogTorus n,
          momentBodyEnvelopePositiveSecant K p t q ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards
      [ae_momentBodyEnvelopePositiveSecant_nonneg_Gibbs K p ht]
      with q hq
    exact max_eq_right hq
  rw [hEq] at hlim
  exact hlim

private theorem integrable_momentBodyMovingJetSlope
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (k : ℕ) :
    Integrable
      (momentTorusJetSlope
        K (momentBodyOptimizer K)
          (momentBodyOptimizer_transport K) p (k + 1))
      (momentTorusBergmanProbability
        K (momentBodyOptimizer K) (k + 1)) := by
  let : IsProbabilityMeasure
      (momentTorusBergmanProbability
        K (momentBodyOptimizer K) (k + 1)) :=
    momentTorusBergmanProbability_isProbability
      K (Nat.zero_lt_succ k) (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K)
  refine
    (integrable_const (BodyScale.canonicalScale K)).mono'
      (continuous_momentTorusJetSlope
        K (momentBodyOptimizer K)
          (momentBodyOptimizer_transport K) p (k + 1)).aestronglyMeasurable
      ?_
  exact Filter.Eventually.of_forall fun q => by
    rw [Real.norm_eq_abs,
      abs_of_nonneg
        (momentTorusJetSlope_nonneg
          K (momentBodyOptimizer K)
            (momentBodyOptimizer_transport K) p (k + 1) q)]
    exact momentTorusJetSlope_le_canonicalScale
      K (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K) p (k + 1) q

private theorem integral_momentBodyMovingJetSlope_le_canonicalScale
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (k : ℕ) :
    (∫ q : LogTorus n,
      momentTorusJetSlope
        K (momentBodyOptimizer K)
          (momentBodyOptimizer_transport K) p (k + 1) q
        ∂(momentTorusBergmanProbability
          K (momentBodyOptimizer K) (k + 1))) ≤
      BodyScale.canonicalScale K := by
  let : IsProbabilityMeasure
      (momentTorusBergmanProbability
        K (momentBodyOptimizer K) (k + 1)) :=
    momentTorusBergmanProbability_isProbability
      K (Nat.zero_lt_succ k) (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K)
  have h := integral_mono
    (integrable_momentBodyMovingJetSlope K p k)
    (integrable_const (BodyScale.canonicalScale K))
    (fun q => momentTorusJetSlope_le_canonicalScale
      K (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K) p (k + 1) q)
  simpa only [ge_iff_le, integral_const, probReal_univ, smul_eq_mul, one_mul] using h

private theorem limsup_momentBodyMovingJetIntegral_ge_sharp
    {n : ℕ} (hn : 0 < n) (K : CenteredBody n)
    (p : LogSpace n) :
    (n : ℝ) * BodyScale.canonicalScale K /
        ((n : ℝ) + 1) ≤
      Filter.limsup
        (fun k : ℕ =>
          ∫ q : LogTorus n,
            momentTorusJetSlope
              K (momentBodyOptimizer K)
                (momentBodyOptimizer_transport K) p (k + 1) q
              ∂(momentTorusBergmanProbability
                K (momentBodyOptimizer K) (k + 1))) atTop := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hevent :=
    eventually_integral_momentTorusJetSlope_Bergman_ge_sharp
      hn K (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K) p hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hevent
  have hshift :
      ∀ᶠ k : ℕ in atTop,
        (n : ℝ) * BodyScale.canonicalScale K /
            ((n : ℝ) + 1) - ε ≤
          ∫ q : LogTorus n,
            momentTorusJetSlope
              K (momentBodyOptimizer K)
                (momentBodyOptimizer_transport K) p (k + 1) q
              ∂(momentTorusBergmanProbability
                K (momentBodyOptimizer K) (k + 1)) := by
    filter_upwards [Filter.eventually_ge_atTop N] with k hk
    exact hN (k + 1) (by omega)
  have hbounded :
      ∀ᶠ k : ℕ in atTop,
        (∫ q : LogTorus n,
          momentTorusJetSlope
            K (momentBodyOptimizer K)
              (momentBodyOptimizer_transport K) p (k + 1) q
            ∂(momentTorusBergmanProbability
              K (momentBodyOptimizer K) (k + 1))) ≤
            BodyScale.canonicalScale K :=
    Filter.Eventually.of_forall
      (integral_momentBodyMovingJetSlope_le_canonicalScale K p)
  have hlim := Filter.le_limsup_of_frequently_le hshift.frequently
    (Filter.isBoundedUnder_of_eventually_le hbounded)
  linarith

private theorem integral_momentBodyEnvelopePositiveSecant_ge_sharp_of_weak
    {n : ℕ} (hn : 0 < n) (K : CenteredBody n)
    (p : LogSpace n)
    (hweak : Tendsto (momentBodyMovingBergmanProbability K) atTop
      (𝓝 (momentBodyZeroGibbsProbability K p)))
    {t : ℝ} (ht : 0 < t) :
    (n : ℝ) * BodyScale.canonicalScale K /
        ((n : ℝ) + 1) ≤
      ∫ q : LogTorus n,
        momentBodyEnvelopePositiveSecant K p t q
          ∂(sourceProbability (momentBodyTorusWeight K p) 0) := by
  apply ge_of_tendsto
    (tendsto_integral_momentBodyClampedTailPositiveSecant
      K p t ht)
  exact Filter.Eventually.of_forall fun r =>
    (limsup_momentBodyMovingJetIntegral_ge_sharp hn K p).trans
      (limsup_momentBodyMovingJetIntegral_le_clampedTail_of_weak
        K p r t ht hweak)

private theorem momentBodySharpJetScale_le_dimension_of_weakProbability
    {n : ℕ} (hn : 0 < n) (K : CenteredBody n)
    (hweak : Tendsto (momentBodyMovingBergmanProbability K) atTop
      (𝓝 (momentBodyZeroGibbsProbability K (0 : LogSpace n)))) :
    (n : ℝ) * BodyScale.canonicalScale K /
      ((n : ℝ) + 1) ≤ (n : ℝ) := by
  have htend :
      Tendsto
        (fun k : ℕ => 1 / ((k : ℝ) + 1))
        atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hcontinuous :
      Continuous
        (fun t : ℝ =>
          (n : ℝ) *
            Real.exp (BodyScale.canonicalScale K * t)) :=
    continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hlimit :
      Tendsto
        (fun k : ℕ =>
          (n : ℝ) * Real.exp
            (BodyScale.canonicalScale K *
              (1 / ((k : ℝ) + 1))))
        atTop (𝓝 (n : ℝ)) := by
    have h := hcontinuous.continuousAt.tendsto.comp htend
    have hzero :
        (n : ℝ) *
            Real.exp (BodyScale.canonicalScale K * 0) =
          (n : ℝ) := by
      simp only [mul_zero, Real.exp_zero, mul_one]
    rw [hzero] at h
    refine h.congr' (Filter.Eventually.of_forall fun k => ?_)
    rfl
  apply ge_of_tendsto hlimit
  exact Filter.Eventually.of_forall fun k => by
    have ht : 0 < (1 / ((k : ℝ) + 1)) := by positivity
    calc
      (n : ℝ) * BodyScale.canonicalScale K /
        ((n : ℝ) + 1) ≤
          ∫ q : LogTorus n,
            momentBodyEnvelopePositiveSecant
              K (0 : LogSpace n) (1 / ((k : ℝ) + 1)) q
              ∂(sourceProbability
                (momentBodyTorusWeight K (0 : LogSpace n)) 0) :=
        integral_momentBodyEnvelopePositiveSecant_ge_sharp_of_weak
          hn K (0 : LogSpace n) hweak ht
      _ ≤ (n : ℝ) * Real.exp
          (BodyScale.canonicalScale K *
            (1 / ((k : ℝ) + 1))) :=
        integral_momentBodyEnvelopePositiveSecant_le_dimension_mul_exp
          K ht

private theorem normalizedVolume_le_sharpConstant_of_momentBodyWeakProbability
    {n : ℕ} (hn : 0 < n) (K : CenteredBody n)
    (hweak : Tendsto (momentBodyMovingBergmanProbability K) atTop
      (𝓝 (momentBodyZeroGibbsProbability K (0 : LogSpace n)))) :
    normalizedVolume K.carrier ≤ sharpConstant n := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hbound : BodyScale.canonicalScale K ≤ (n : ℝ) + 1 := by
    nlinarith [(div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mp
      (momentBodySharpJetScale_le_dimension_of_weakProbability hn K hweak)]
  change normalizedVolume K.carrier ≤
    ((n : ℝ) + 1) ^ n / (n.factorial : ℝ)
  apply (le_div_iff₀ (by positivity : 0 < (n.factorial : ℝ))).mpr
  simpa only [BodyScale.canonicalScale_pow hn K, mul_comm] using
    pow_le_pow_left₀ (BodyScale.canonicalScale_pos K).le hbound n

end BergmanJetPortmanteauActualVolumeBridge

namespace MomentWeakBergmanProbabilityEndpoint

open Set Function Filter MeasureTheory
open BergmanMonomials BergmanNormalization LatticeAsymptotics MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity MomentWeakBergman MomentWeakGlobalKernel
open scoped BigOperators ENNReal Topology

private theorem normalizedMonomialDensity_momentNormalized_integrable
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) :
    Integrable
      (normalizedMonomialDensity K k (momentNormalizedPotential F) u)
      (volume : Measure (Space n)) := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  exact
    (integrable_monomialWeight_momentNormalized_of_mem_interior
      F htransport u.property.1 hkreal).div_const _

private theorem normalizedMonomialDensity_momentNormalized_pos
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) (x : Space n) :
    0 < normalizedMonomialDensity
      K k (momentNormalizedPotential F) u x := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  unfold normalizedMonomialDensity
  apply div_pos
  · exact Real.exp_pos _
  · exact monomialIntegral_momentNormalized_pos
      F htransport u.property.1 hkreal

private theorem integral_normalizedMonomialDensity_momentNormalized
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) :
    (∫ x : Space n,
      normalizedMonomialDensity
        K k (momentNormalizedPotential F) u x
        ∂(volume : Measure (Space n))) = 1 := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  unfold normalizedMonomialDensity
  rw [MeasureTheory.integral_div]
  change
    monomialNormSquared k (u : Space n)
        (momentNormalizedPotential F) /
      monomialNormSquared k (u : Space n)
        (momentNormalizedPotential F) = 1
  apply div_self
  exact
    (monomialIntegral_momentNormalized_pos
      F htransport u.property.1 hkreal).ne'

private theorem weightedDiagonalKernel_momentNormalized_integrable
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    Integrable
      (weightedDiagonalKernel K k (momentNormalizedPotential F))
      (volume : Measure (Space n)) := by
  let := (monomialIndex_finite K hk).fintype
  unfold weightedDiagonalKernel
  simp_rw [tsum_fintype]
  exact integrable_finsetSum Finset.univ
    (fun u _ => normalizedMonomialDensity_momentNormalized_integrable
      K hk F htransport u)

private theorem integral_weightedDiagonalKernel_momentNormalized
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    (∫ x : Space n,
      weightedDiagonalKernel K k (momentNormalizedPotential F) x
        ∂(volume : Measure (Space n))) =
      (bergmanDimension K k : ℝ) := by
  let := (monomialIndex_finite K hk).fintype
  unfold weightedDiagonalKernel
  simp_rw [tsum_fintype]
  rw [MeasureTheory.integral_finsetSum]
  · simp_rw [integral_normalizedMonomialDensity_momentNormalized
      K hk F htransport]
    simp only [Finset.sum_const, Finset.card_univ, fintypeCard_eq_ncard, nsmul_eq_mul, mul_one,
      bergmanDimension, Nat.card_eq_fintype_card]
  · intro u _
    exact normalizedMonomialDensity_momentNormalized_integrable
      K hk F htransport u

private theorem normalizedDiagonalDensity_momentNormalized_integrable
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    Integrable
      (normalizedDiagonalDensity K k (momentNormalizedPotential F))
      (volume : Measure (Space n)) := by
  exact
    (weightedDiagonalKernel_momentNormalized_integrable
      K hk F htransport).div_const _

private theorem normalizedDiagonalDensity_momentNormalized_pos
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (x : Space n) :
    0 < normalizedDiagonalDensity
      K k (momentNormalizedPotential F) x := by
  unfold normalizedDiagonalDensity
  exact div_pos
    (weightedDiagonalKernel_momentNormalized_pos
      K hk F htransport x)
    (by exact_mod_cast bergmanDimension_pos K hk)

private theorem integral_normalizedDiagonalDensity_momentNormalized
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    (∫ x : Space n,
      normalizedDiagonalDensity K k
        (momentNormalizedPotential F) x
      ∂(volume : Measure (Space n))) = 1 := by
  unfold normalizedDiagonalDensity
  rw [MeasureTheory.integral_div,
    integral_weightedDiagonalKernel_momentNormalized
      K hk F htransport]
  apply div_self
  exact_mod_cast (bergmanDimension_pos K hk).ne'

private theorem normalizedBergmanMeasure_momentNormalized_univ
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    normalizedBergmanMeasure
      K k (momentNormalizedPotential F) Set.univ = 1 := by
  unfold normalizedBergmanMeasure
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (normalizedDiagonalDensity_momentNormalized_integrable
      K hk F htransport)
    (Filter.Eventually.of_forall fun x =>
      (normalizedDiagonalDensity_momentNormalized_pos
        K hk F htransport x).le),
    integral_normalizedDiagonalDensity_momentNormalized
      K hk F htransport]
  exact ENNReal.ofReal_one

private theorem normalizedBergmanMeasure_momentNormalized_isProbability
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    IsProbabilityMeasure
      (normalizedBergmanMeasure
        K k (momentNormalizedPotential F)) :=
  ⟨normalizedBergmanMeasure_momentNormalized_univ
    K hk F htransport⟩

private theorem momentNormalizedDensity_div_volume_eq_gibbsDensity
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) (x : Space n) :
    Real.exp (-momentNormalizedPotential F x) /
        normalizedVolume K.carrier =
      WeightedPoincare.normalizedDensity F.potential x := by
  rw [exp_neg_momentNormalizedPotential F x]
  change
    (normalizedVolume K.carrier /
      finiteEnergySourcePartition F * Real.exp (-F.potential x)) /
      normalizedVolume K.carrier =
        Real.exp (-F.potential x) /
          finiteEnergySourcePartition F
  field_simp [K.volume_pos.ne',
    (finiteEnergySourcePartition_pos F).ne']

end MomentWeakBergmanProbabilityEndpoint

namespace BergmanJetBergmanProbabilityTransfer

open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert BergmanMonomials BergmanNormalization
open JetEnvelopeSlopeConvergence LogPartitionConvexity MomentOptimizer MomentWeakFirstVariation
open MomentRegularity MomentWeakBergman MomentWeakBergmanProbabilityEndpoint
open BergmanJetPartitionEndpoint BergmanJetTorusSlopeBridge
open scoped BigOperators ENNReal Topology

private def momentWeakTorusBergmanDensity {n : ℕ}
    (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (k : ℕ) (q : LogTorus n) : ℝ :=
  normalizedDiagonalDensity K k (momentNormalizedPotential F) q.1

private def momentWeakTorusGibbsDensity {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (q : LogTorus n) : ℝ :=
  WeightedPoincare.normalizedDensity F.potential q.1

private def momentWeakTorusGibbsProbability {n : ℕ}
    {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) : Measure (LogTorus n) :=
  (finiteEnergySourceGibbsProbability F).prod (angularMeasure n)

private theorem momentTorusBergmanProbability_eq_base_withDensity
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K) :
    momentTorusBergmanProbability K F k =
      (sourceTorusBaseMeasure n).withDensity
        (fun q : LogTorus n =>
          ENNReal.ofReal (momentWeakTorusBergmanDensity K F k q)) := by
  let base : Measure (LogTorus n) := sourceTorusBaseMeasure n
  let w : LogTorus n → ℝ≥0∞ :=
    fun q => radialWeight k (momentNormalizedPotential F) q.1
  let d : LogTorus n → ℝ≥0∞ := fun q =>
    ENNReal.ofReal
      (diagonalKernel K k (momentNormalizedPotential F) q.1 /
        (bergmanDimension K k : ℝ))
  have hwmeas : Measurable w :=
    (radialWeight_measurable k
      (continuous_momentNormalizedPotential F)).comp measurable_fst
  have hdmeas : Measurable d :=
    ENNReal.measurable_ofReal.comp
      (((continuous_momentDiagonalKernel K hk F).div_const
        (bergmanDimension K k : ℝ)).comp continuous_fst).measurable
  have hweight :
      weightedTorusMeasure k (momentNormalizedPotential F) =
        base.withDensity w := by
    simpa [base, w, sourceTorusBaseMeasure] using
      weightedTorusMeasure_eq_withDensity k
        (continuous_momentNormalizedPotential F)
  change
    (weightedTorusMeasure k
      (momentNormalizedPotential F)).withDensity d =
      base.withDensity
        (fun q => ENNReal.ofReal
          (momentWeakTorusBergmanDensity K F k q))
  rw [hweight, ← MeasureTheory.withDensity_mul base hwmeas hdmeas]
  congr 1
  funext q
  dsimp [w, d]
  unfold radialWeight momentWeakTorusBergmanDensity
    normalizedDiagonalDensity
  rw [weightedDiagonalKernel_eq_exp_neg_mul_diagonalKernel K hk]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  ring

private theorem momentWeakTorusGibbsProbability_eq_base_withDensity
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    momentWeakTorusGibbsProbability F =
      (sourceTorusBaseMeasure n).withDensity
        (fun q : LogTorus n =>
          ENNReal.ofReal (momentWeakTorusGibbsDensity F q)) := by
  have hmeas : Measurable
      (fun x : Space n => ENNReal.ofReal
        (WeightedPoincare.normalizedDensity F.potential x)) :=
    ENNReal.measurable_ofReal.comp
      ((Real.continuous_exp.comp F.potential.continuous.neg).div_const
        (WeightedPoincare.partition F.potential)).measurable
  unfold momentWeakTorusGibbsProbability
    finiteEnergySourceGibbsProbability
    WeightedPoincare.normalizedMeasure
    sourceTorusBaseMeasure momentWeakTorusGibbsDensity
  exact MeasureTheory.prod_withDensity_left hmeas

private theorem momentWeakTorusGibbsDensity_body_eq_zeroTime
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (q : LogTorus n) :
    momentWeakTorusGibbsDensity
      (momentBodyOptimizer K) q =
        sourceNormalizedDensity (momentBodyTorusWeight K p) 0 q := by
  unfold momentWeakTorusGibbsDensity
    sourceNormalizedDensity sourceTimeDensity
  rw [momentBodyTorusWeight_zero]
  change
    WeightedPoincare.normalizedDensity
      (momentBodyOptimizer K).potential q.1 =
      Real.exp
        (-momentNormalizedPotential (momentBodyOptimizer K) q.1) /
        momentBodyPartition K p 0
  rw [momentBodyPartition_zero]
  exact (momentNormalizedDensity_div_volume_eq_gibbsDensity
    (momentBodyOptimizer K) q.1).symm

private theorem momentWeakTorusGibbsProbability_body_eq_zeroTime
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) :
    momentWeakTorusGibbsProbability
      (momentBodyOptimizer K) =
        sourceProbability (momentBodyTorusWeight K p) 0 := by
  rw [momentWeakTorusGibbsProbability_eq_base_withDensity]
  unfold sourceProbability
  congr 1
  funext q
  rw [momentWeakTorusGibbsDensity_body_eq_zeroTime K p q]

end BergmanJetBergmanProbabilityTransfer

namespace BergmanJetRadialHaarWeakProbabilityLift

open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert BergmanNormalization LogPartitionConvexity MomentOptimizer
open MomentWeakFirstVariation MomentFirstVariation MomentTargetGeodesic MomentRegularity
open MomentWeakBergman MomentWeakBergmanProbabilityEndpoint BergmanJetPartitionEndpoint
open BergmanJetTorusSlopeBridge BergmanJetBergmanProbabilityTransfer
open BergmanJetPortmanteauActualVolumeBridge
open scoped BigOperators ENNReal NNReal Topology BoundedContinuousFunction

private def momentMovingRadialBergmanProbability
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (k : ℕ) : ProbabilityMeasure (Space n) :=
  ⟨normalizedBergmanMeasure
      K (k + 1) (momentNormalizedPotential F),
    normalizedBergmanMeasure_momentNormalized_isProbability
      K (Nat.zero_lt_succ k) F htransport⟩

private def momentRadialGibbsProbability
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    ProbabilityMeasure (Space n) :=
  ⟨finiteEnergySourceGibbsProbability F,
    finiteEnergySourceGibbsProbability_isProbability F⟩

private def momentNormalizedAngularHaarProbability (n : ℕ) :
    ProbabilityMeasure (AngularTorus n) :=
  ⟨angularMeasure n, angularMeasure_isProbability n⟩

private theorem momentTorusBergmanProbability_eq_normalizedRadial_prod_angular
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K) :
    momentTorusBergmanProbability K F k =
      (normalizedBergmanMeasure
        K k (momentNormalizedPotential F)).prod
          (angularMeasure n) := by
  have hmeas : Measurable
      (fun x : Space n =>
        ENNReal.ofReal
          (normalizedDiagonalDensity
            K k (momentNormalizedPotential F) x)) :=
    ENNReal.measurable_ofReal.comp
      (BergmanJetSlope.continuous_normalizedDiagonalDensity
        K hk (continuous_momentNormalizedPotential F)).measurable
  rw [momentTorusBergmanProbability_eq_base_withDensity K hk F]
  change
    ((volume : Measure (Space n)).prod (angularMeasure n)).withDensity
        (fun q : LogTorus n =>
          ENNReal.ofReal
            (normalizedDiagonalDensity
              K k (momentNormalizedPotential F) q.1)) =
      ((volume : Measure (Space n)).withDensity
        (fun x : Space n =>
          ENNReal.ofReal
            (normalizedDiagonalDensity
              K k (momentNormalizedPotential F) x))).prod
          (angularMeasure n)
  exact (MeasureTheory.prod_withDensity_left hmeas).symm

private theorem integral_normalizedBergmanMeasure_momentNormalized
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (f : Space n → ℝ) :
    (∫ x : Space n, f x
      ∂(normalizedBergmanMeasure
        K k (momentNormalizedPotential F))) =
      ∫ x : Space n,
        f x * normalizedDiagonalDensity
          K k (momentNormalizedPotential F) x
          ∂(volume : Measure (Space n)) := by
  have hmeas : Measurable
      (fun x : Space n =>
        ENNReal.ofReal
          (normalizedDiagonalDensity
            K k (momentNormalizedPotential F) x)) :=
    ENNReal.measurable_ofReal.comp
      (BergmanJetSlope.continuous_normalizedDiagonalDensity
        K hk (continuous_momentNormalizedPotential F)).measurable
  have hfinite :
      ∀ᵐ x : Space n ∂(volume : Measure (Space n)),
        ENNReal.ofReal
          (normalizedDiagonalDensity
            K k (momentNormalizedPotential F) x) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [normalizedBergmanMeasure,
    integral_withDensity_eq_integral_toReal_smul hmeas hfinite]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal
    (normalizedDiagonalDensity_momentNormalized_pos
      K hk F htransport x).le]
  simp only [smul_eq_mul, mul_comm]

private theorem tendsto_momentMovingRadialBergmanProbability_of_tests
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (htests : ∀ f : Space n →ᵇ ℝ,
      Tendsto
        (fun k : ℕ =>
          ∫ x : Space n,
            f x * normalizedDiagonalDensity
              K (k + 1) (momentNormalizedPotential F) x
              ∂(volume : Measure (Space n)))
        atTop
        (𝓝 (∫ x : Space n, f x
          ∂(finiteEnergySourceGibbsProbability F)))) :
    Tendsto
      (momentMovingRadialBergmanProbability K F htransport)
      atTop (𝓝 (momentRadialGibbsProbability F)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  change
    Tendsto
      (fun k : ℕ =>
        ∫ x : Space n, f x
          ∂(normalizedBergmanMeasure
            K (k + 1) (momentNormalizedPotential F)))
      atTop
      (𝓝 (∫ x : Space n, f x
        ∂(finiteEnergySourceGibbsProbability F)))
  have hEq :
      (fun k : ℕ =>
        ∫ x : Space n, f x
          ∂(normalizedBergmanMeasure
            K (k + 1) (momentNormalizedPotential F))) =
        fun k : ℕ =>
          ∫ x : Space n,
            f x * normalizedDiagonalDensity
              K (k + 1) (momentNormalizedPotential F) x
              ∂(volume : Measure (Space n)) := by
    funext k
    exact integral_normalizedBergmanMeasure_momentNormalized
      K (Nat.zero_lt_succ k) F htransport f
  rw [hEq]
  exact htests f

private theorem momentBodyMovingBergmanProbability_eq_radial_prod_angular
    {n : ℕ} (K : CenteredBody n) (k : ℕ) :
    momentBodyMovingBergmanProbability K k =
      (momentMovingRadialBergmanProbability
        K (momentBodyOptimizer K)
          (momentBodyOptimizer_transport K) k).prod
            (momentNormalizedAngularHaarProbability n) := by
  apply Subtype.ext
  exact momentTorusBergmanProbability_eq_normalizedRadial_prod_angular
    K (Nat.zero_lt_succ k) (momentBodyOptimizer K)

private theorem momentBodyZeroGibbsProbability_eq_radial_prod_angular
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) :
    momentBodyZeroGibbsProbability K p =
      (momentRadialGibbsProbability
        (momentBodyOptimizer K)).prod
          (momentNormalizedAngularHaarProbability n) := by
  apply Subtype.ext
  change
    sourceProbability (momentBodyTorusWeight K p) 0 =
      (finiteEnergySourceGibbsProbability
        (momentBodyOptimizer K)).prod (angularMeasure n)
  exact
    (momentWeakTorusGibbsProbability_body_eq_zeroTime K p).symm

private theorem momentBodyBergmanWeakProbabilityConvergence_of_radial
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n)
    (hrad : Tendsto
      (momentMovingRadialBergmanProbability
        K (momentBodyOptimizer K)
          (momentBodyOptimizer_transport K))
      atTop
      (𝓝 (momentRadialGibbsProbability
        (momentBodyOptimizer K)))) :
    Tendsto (momentBodyMovingBergmanProbability K) atTop
      (𝓝 (momentBodyZeroGibbsProbability K p)) := by
  have hpair :
      Tendsto
        (fun k : ℕ =>
          (momentMovingRadialBergmanProbability
            K (momentBodyOptimizer K)
              (momentBodyOptimizer_transport K) k,
           momentNormalizedAngularHaarProbability n))
        atTop
        (𝓝 (momentRadialGibbsProbability
              (momentBodyOptimizer K),
            momentNormalizedAngularHaarProbability n)) :=
    hrad.prodMk_nhds tendsto_const_nhds
  have hproduct :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp hpair
  change
    Tendsto (momentBodyMovingBergmanProbability K)
      atTop (𝓝 (momentBodyZeroGibbsProbability K p))
  have hsequence :
      momentBodyMovingBergmanProbability K =
        fun k : ℕ =>
          (momentMovingRadialBergmanProbability
            K (momentBodyOptimizer K)
              (momentBodyOptimizer_transport K) k).prod
                (momentNormalizedAngularHaarProbability n) := by
    funext k
    exact momentBodyMovingBergmanProbability_eq_radial_prod_angular
      K k
  rw [hsequence,
    momentBodyZeroGibbsProbability_eq_radial_prod_angular]
  exact hproduct

private theorem momentBodyBergmanWeakProbabilityConvergence_of_radial_tests
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n)
    (htests : ∀ f : Space n →ᵇ ℝ,
      Tendsto
        (fun k : ℕ =>
          ∫ x : Space n,
            f x * normalizedDiagonalDensity
              K (k + 1)
                (momentNormalizedPotential (momentBodyOptimizer K)) x
              ∂(volume : Measure (Space n)))
        atTop
        (𝓝 (∫ x : Space n, f x
          ∂(finiteEnergySourceGibbsProbability
            (momentBodyOptimizer K))))) :
    Tendsto (momentBodyMovingBergmanProbability K) atTop
      (𝓝 (momentBodyZeroGibbsProbability K p)) :=
  momentBodyBergmanWeakProbabilityConvergence_of_radial K p
    (tendsto_momentMovingRadialBergmanProbability_of_tests
      K (momentBodyOptimizer K)
        (momentBodyOptimizer_transport K) htests)

end BergmanJetRadialHaarWeakProbabilityLift

end Ehrhart

end

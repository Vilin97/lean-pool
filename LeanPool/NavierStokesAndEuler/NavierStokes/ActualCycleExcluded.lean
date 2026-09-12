/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectionStep
public import LeanPool.NavierStokesAndEuler.NavierStokes.GaugeExcludedBounds
import LeanPool.NavierStokesAndEuler.NavierStokes.MeanStageRegularity

/-!
# Every-power bounds for the literal cycle's axisymmetric alias

The three newly evaluated aliases use one fixed similarity gauge, strip,
covering index, and fast operator. Their bounds are derived from primitive
state regularity and ordinary cumulative/covariance estimates.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualCycleExcluded

open Set Function Filter WeightedClasses MeanIncrementBounds CorrectionState
open CorrectionStep VariableGaugeMean LocalSignedRequest MeanStateRegularity
open scoped ContDiff Topology BigOperators

/-- Point: an abbreviation for `MeanStateRegularity.Point`. -/
abbrev Point := MeanStateRegularity.Point

/-- Fixed numerical and geometric data for the actual similarity estimates. -/
structure SimilarityData where
  /-- Step-size parameter of `SimilarityData`, of type `ℝ`. -/
  h : ℝ
  h_pos : 0 < h
  /-- Inner of `SimilarityData`, of type `ℝ`. -/
  inner : ℝ
  /-- Outer of `SimilarityData`, of type `ℝ`. -/
  outer : ℝ
  inner_pos : 0 < inner
  inner_lt_outer : inner < outer
  /-- Left weight of `SimilarityData`, of type `ℝ`. -/
  leftWeight : ℝ
  /-- Right weight of `SimilarityData`, of type `ℝ`. -/
  rightWeight : ℝ
  left_pos : 0 < leftWeight
  right_pos : 0 < rightWeight
  /-- Base scale of `SimilarityData`, of type `ℝ`. -/
  baseScale : ℝ
  baseScale_ne : baseScale ≠ 0
  /-- Region of `SimilarityData`, of type `SlowRegion (2 * h)`. -/
  region : SlowRegion (2 * h)
  /-- Index of `SimilarityData`, of type `ℕ → ℕ`. -/
  index : ℕ → ℕ
  /-- Gap of `SimilarityData`, of type `ℕ`. -/
  gap : ℕ
  index_lower : ∀ n, ChartScales.nativeIndex h n ≤ index n + gap
  index_upper : ∀ n, index n ≤ ChartScales.nativeIndex h n + gap
  /-- Slow of `SimilarityData`, of type `ℕ → ℝ`. -/
  slow : ℕ → ℝ
  slow_one : ∀ n, 1 ≤ slow n
  slow_scale : ∀ n, ChartScales.S n ≤ slow n

/-- Strip, given by `GaugeExcludedBounds.actualStrip (b := d.outer) d.region d.inner_pos
d.left_pos d.right_pos d.h_pos d.slow d.slow_one`. -/
noncomputable def SimilarityData.strip (d : SimilarityData) : StripData Point :=
  GaugeExcludedBounds.actualStrip (b := d.outer) d.region d.inner_pos d.left_pos d.right_pos
    d.h_pos d.slow d.slow_one

/-- Gauge, given by `GaugeExcludedBounds.actualGauge d.h d.inner d.outer d.baseScale
d.inner_lt_outer d.index`. -/
noncomputable def SimilarityData.gauge (d : SimilarityData) : GaugeData TorusInverse.Plane :=
  GaugeExcludedBounds.actualGauge d.h d.inner d.outer d.baseScale d.inner_lt_outer d.index

/-- These are equalities of the actual data used by the cycle, not
hypotheses on any excluded output field. -/
structure Compatible {ι : Type} (d : SimilarityData) (p : CycleParameters ι)
    (c : Context Point) : Prop where
  gauge : p.gauge = d.gauge
  strip : p.strip = d.strip
  time : p.timeExponent = d.h
  index : p.commonIndex = d.index
  fast : c.operators.fastCoefficient =
    fun n => ChartScales.Tg ^ d.index n * ChartScales.Q n ^ (1 + d.h)
  temporal : c.operators.vT = (0, (0, TorusInverse.vector .temporal))

section ExactStages

variable {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
  (c : Context Point) (u : State Point)

/-- Regularity of the two states at which the new aliases are evaluated.
The original rank geometry is reused after recomputing the actual debt. -/
theorem stage_primitives {coord : ℝ} (U : SlowRegion coord)
    (ha : 0 < p.gauge.radial.inner) (hd : 0 < p.gauge.radial.exponent)
    (hell : ∀ n, p.gauge.length n = qLength coord)
    (H : PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c u)
    (hX₁ : ∀ i j, GaugeMomentBalances.MovingField U p.gauge.radial.inner p.gauge.radial.outer
      (SignedMeanGain.covarianceIncrement u.oscillation (p.particularVelocity v c u) i j))
    (hX₂ : ∀ i j, GaugeMomentBalances.MovingField U p.gauge.radial.inner p.gauge.radial.outer
      (SignedMeanGain.covarianceIncrement (p.afterParticular v c u).oscillation
        (p.signedVelocity v c u) i j))
    (hrank : LocalRankDefect.RankGeometry p.gauge p.rank U.carrier c u) :
    PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c (p.afterSigned v c u) ∧
      PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c (p.afterRank v c u) := by
  have H₁ : PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c (p.afterParticular v c u) :=
    H.waveStage p.gauge (p.particularVelocity v c u) (p.particularPressure v c u)
      (p.particularGaussian v c u) hX₁
  have H₂ : PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c (p.afterSigned v c u) :=
    H₁.waveStage p.gauge (p.signedVelocity v c u) (p.signedPressure v c u)
      (p.signedGaussian v c u) hX₂
  have HT := MeanStageRegularity.temporalStage_primitive H₂ ha hd hell rfl
    p.timeExponent p.commonIndex p.axial
  have HG := MeanStageRegularity.rankGeometry_for_state HT ha p.gauge.radial.inner_lt_outer hrank
  exact ⟨H₂, MeanStageRegularity.rankStage_primitive HT HG hell p.axial⟩

theorem afterRank_cumulative_of_next {s : StripData Point}
    (hnext : CorrectionState.CumulativeBounds s (p.next v c u)) :
    CorrectionState.CumulativeBounds s (p.afterRank v c u) :=
  ⟨hnext.velocity, hnext.pressure⟩

/-- The covariance is updated only by the two actual wave increments.
Temporal and rank mean changes leave this covariance unchanged. -/
theorem afterRank_covariance_mem {s : StripData Point} {γ : ℝ}
    (hW : ∀ i j, MeanClass s γ (u.covariance i j))
    (hX₁ : ∀ i j, MeanClass s γ
      (SignedMeanGain.covarianceIncrement u.oscillation (p.particularVelocity v c u) i j))
    (hX₂ : ∀ i j, MeanClass s γ
      (SignedMeanGain.covarianceIncrement (p.afterParticular v c u).oscillation
        (p.signedVelocity v c u) i j)) :
    ∀ i j, MeanClass s γ ((p.afterRank v c u).covariance i j) := by
  have H₁ : ∀ i j, MeanClass s γ ((p.afterParticular v c u).covariance i j) := by
    intro i j
    change MeanClass s γ ((SignedMeanGain.waveStage p.gauge c u
      (p.particularVelocity v c u) (p.particularPressure v c u)
      (p.particularGaussian v c u)).covariance i j)
    rw [SignedMeanGain.waveStage_covariance]
    exact (hW i j).add (hX₁ i j)
  have H₂ : ∀ i j, MeanClass s γ ((p.afterSigned v c u).covariance i j) := by
    intro i j
    change MeanClass s γ ((SignedMeanGain.waveStage p.gauge c (p.afterParticular v c u)
      (p.signedVelocity v c u) (p.signedPressure v c u)
      (p.signedGaussian v c u)).covariance i j)
    rw [SignedMeanGain.waveStage_covariance]
    exact (H₁ i j).add (hX₂ i j)
  intro i j
  change MeanClass s γ ((rankStageState p.gauge p.rank p.axial c
    (temporalStageState p.gauge p.timeExponent p.commonIndex p.axial c
      (p.afterSigned v c u))).covariance i j)
  rw [LocalRankDefect.rankStage_covariance, GaugeDebtIncrement.temporalStage_covariance]
  exact H₂ i j

theorem nextAxisymmetricAlias_eq (axis : AxisymmetricAlias) :
    p.nextAxisymmetricAlias v c u axis = axis +
      (fun n x => temporalAliasState p.gauge p.timeExponent p.commonIndex c (p.afterSigned v c u) n
          (x, 0)) +
      ((fun n x => pressureAliasState p.gauge c (p.afterRank v c u) n (x, 0)) -
        (fun n x => pressureAliasState p.gauge c u n (x, 0))) := rfl

end ExactStages

private theorem meanClass_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : StripData Point} {β : ℝ} {f g : ℕ → Point → E}
    (hf : MeanClass s β f) (hg : MeanClass s β g) : MeanClass s β (f - g) := by
  have hn := hg.map (-ContinuousLinearMap.id ℝ E)
  have he := hf.add hn
  simp only [sub_eq_add_neg, _root_.neg_apply, ContinuousLinearMap.id_apply] at he ⊢
  exact he

section ActualBounds

variable {ι : Type} (d : SimilarityData) (p : CycleParameters ι) (v : CycleCoefficients ι)
  (c : Context Point) (u : State Point) (matchData : Compatible d p c)

include matchData

/-- The three new aliases are estimated by `GaugeExcludedBounds` for the
same concrete similarity data. The after-signed and after-rank primitive
certificates are derived, and the old pressure alias is subtracted. -/
theorem nextAxisymmetricAlias_all_powers {κ α γ : ℝ}
    (H : PrimitiveData d.region d.inner d.outer c u)
    (hX₁ : ∀ i j, GaugeMomentBalances.MovingField d.region d.inner d.outer
      (SignedMeanGain.covarianceIncrement u.oscillation (p.particularVelocity v c u) i j))
    (hX₂ : ∀ i j, GaugeMomentBalances.MovingField d.region d.inner d.outer
      (SignedMeanGain.covarianceIncrement (p.afterParticular v c u).oscillation
        (p.signedVelocity v c u) i j))
    (hrank : LocalRankDefect.RankGeometry p.gauge p.rank d.region.carrier c u)
    (ho : OperatorBounds p.strip c.operators κ) (hb : BaseBounds p.strip c.base)
    (hu : CorrectionState.CumulativeBounds p.strip u)
    (hnext : CorrectionState.CumulativeBounds p.strip (p.next v c u))
    (hW : ∀ i j, MeanClass p.strip γ (u.covariance i j))
    (hCov₁ : ∀ i j, MeanClass p.strip γ
      (SignedMeanGain.covarianceIncrement u.oscillation (p.particularVelocity v c u) i j))
    (hCov₂ : ∀ i j, MeanClass p.strip γ
      (SignedMeanGain.covarianceIncrement (p.afterParticular v c u).oscillation
        (p.signedVelocity v c u) i j))
    (hraw : MeanClass p.strip α ((p.afterSigned v c u).axialResidual c))
    (axis : AxisymmetricAlias) (haxis : ∀ β : ℝ, MeanClass p.strip β axis) :
    ∀ β : ℝ, MeanClass p.strip β (p.nextAxisymmetricAlias v c u axis) := by
  rw [matchData.strip] at ho hb hu hnext hW hCov₁ hCov₂ hraw haxis ⊢
  have hi : p.gauge.radial.inner = d.inner := by rw [matchData.gauge]; rfl
  have ho' : p.gauge.radial.outer = d.outer := by rw [matchData.gauge]; rfl
  have ha : 0 < p.gauge.radial.inner := by rw [hi]; exact d.inner_pos
  have hd : 0 < p.gauge.radial.exponent := by
    rw [matchData.gauge]
    exact ChartScales.radialExponent_pos d.h d.h_pos.le
  have hell : ∀ n, p.gauge.length n = qLength (2 * d.h) := by
    intro n
    rw [matchData.gauge]
    rfl
  have HP : PrimitiveData d.region p.gauge.radial.inner p.gauge.radial.outer c u := by
    simpa only [hi, ho'] using H
  have hXP₁ : ∀ i j, GaugeMomentBalances.MovingField d.region p.gauge.radial.inner
      p.gauge.radial.outer
      (SignedMeanGain.covarianceIncrement u.oscillation (p.particularVelocity v c u) i j) := by
    simpa only [hi, ho'] using hX₁
  have hXP₂ : ∀ i j, GaugeMomentBalances.MovingField d.region p.gauge.radial.inner
      p.gauge.radial.outer
      (SignedMeanGain.covarianceIncrement (p.afterParticular v c u).oscillation
        (p.signedVelocity v c u) i j) := by
    simpa only [hi, ho'] using hX₂
  obtain ⟨HS, HR⟩ := stage_primitives p v c u d.region ha hd hell HP hXP₁ hXP₂ hrank
  rw [hi, ho'] at HS HR
  have hfixed : (reconstructState d.gauge c (p.afterSigned v c u)).pressure =
      (p.afterSigned v c u).pressure := by
    rw [← matchData.gauge]
    rfl
  have hcum := afterRank_cumulative_of_next p v c u hnext
  have hcov := afterRank_covariance_mem p v c u hW hCov₁ hCov₂
  intro β
  have htemporal : MeanClass d.strip β
      (fun n x => temporalAliasState d.gauge d.h d.index c (p.afterSigned v c u) n (x, 0)) :=
    (GaugeExcludedBounds.temporalAliasState_mean_bounds d.region d.inner_pos d.inner_lt_outer
      d.left_pos d.right_pos d.h_pos d.baseScale_ne d.index d.gap d.index_lower d.index_upper
      d.slow d.slow_one d.slow_scale c (p.afterSigned v c u) HS hfixed
      matchData.fast matchData.temporal hraw β).1
  have hpressureNew : MeanClass d.strip β
      (fun n x => pressureAliasState d.gauge c (p.afterRank v c u) n (x, 0)) :=
    (GaugeExcludedBounds.pressureAliasState_mean_bounds d.region d.inner_pos d.inner_lt_outer
      d.left_pos d.right_pos d.h_pos d.baseScale_ne d.index d.gap d.index_lower
      d.slow d.slow_one d.slow_scale c (p.afterRank v c u) HR ho hb hcum hcov β).1
  have hpressureOld : MeanClass d.strip β
      (fun n x => pressureAliasState d.gauge c u n (x, 0)) :=
    (GaugeExcludedBounds.pressureAliasState_mean_bounds d.region d.inner_pos d.inner_lt_outer
      d.left_pos d.right_pos d.h_pos d.baseScale_ne d.index d.gap d.index_lower
      d.slow d.slow_one d.slow_scale c u H ho hb hu hW β).1
  rw [nextAxisymmetricAlias_eq, matchData.gauge, matchData.time, matchData.index]
  exact ((haxis β).add htemporal).add (meanClass_sub hpressureNew hpressureOld)

end ActualBounds

end NavierStokes.ActualCycleExcluded

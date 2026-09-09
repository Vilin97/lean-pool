/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleExcluded
import LeanPool.NavierStokesAndEuler.NavierStokes.CrossBasedMeanComposition
import LeanPool.NavierStokesAndEuler.NavierStokes.CycleMeanEquation
import LeanPool.NavierStokesAndEuler.NavierStokes.MeanStageRegularity
import LeanPool.NavierStokesAndEuler.NavierStokes.SignedCrossDefectClass

/-!
# Analytic preservation for the literal correction cycle

The wave inputs below are estimates and local identities for the two actual
constructed increments.  The full residual, mean, debt, covariance, and
stored-error conclusions are derived for `CycleState.step`.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.CorrectionAnalyticStep

open Set Filter Function
open WeightedClasses MeanIncrementBounds CorrectionState CorrectionStep
open VariableGaugeMean LocalSignedRequest
open scoped ContDiff Topology BigOperators


/-- Point: an abbreviation for `CorrectionStep.CyclePoint`. -/
abbrev Point := CorrectionStep.CyclePoint

/-- Outputs of the two native constructions, on their literal current
source and request.  No complete updated residual or mean estimate is an
input to this record. -/
structure WaveData {ι : Type} (G : SignedMeanGain.Geometry)
    (p : CycleParameters ι) (v : CycleCoefficients ι) (c : Context Point) (u : State Point)
    (P : ι → ℕ → Point → ℝ) (S : ι → ℕ → Set Point) (σ κ : ℝ) : Prop where
  carrier : ∀ l, SameCarrier ((v).blocks l) ((p).signedBlock v c u l)
  particular : ∀ i j, LabelSumBounds.UniformWaveClass (p).strip P (1/2+σ)
    (fun l n z => ((p).particularBlock v c u l).velocity n i j z)
  tangent : ∀ i j, LabelSumBounds.UniformWaveClass (p).strip P (1/2+σ-κ)
    (fun l n z => ((p).signedTangent v c u l).velocity n i j z)
  curl : ∀ i j, LabelSumBounds.UniformWaveClass (p).strip P (1+σ-2*κ)
    (fun l n z => ((p).signedCurl v c u l).velocity n i j z)
  particularPressure : ∀ j, LabelSumBounds.UniformWaveClass (p).strip P (1+σ)
    (fun l n z => ((p).particularBlock v c u l).pressure n j z)
  signedPressure : ∀ j, LabelSumBounds.UniformWaveClass (p).strip P (1+σ-κ)
    (fun l n z => ((p).signedBlock v c u l).pressure n j z)
  particularSmooth : ∀ l n i, HarmonicResidual.SmoothCoefficients G.domain
    (((p).particularBlock v c u l).velocity n i)
  signedSmooth : ∀ l n i, HarmonicResidual.SmoothCoefficients G.domain
    (((p).signedBlock v c u l).velocity n i)
  particularPressureSmooth : ∀ l n, HarmonicResidual.SmoothCoefficients G.domain
    (((p).particularBlock v c u l).pressure n)
  signedPressureSmooth : ∀ l n, HarmonicResidual.SmoothCoefficients G.domain
    (((p).signedBlock v c u l).pressure n)
  particularGaussianSmooth : ∀ l n i, HarmonicResidual.SmoothCoefficients G.domain
    (((p).particularGaussianBlock v c u l).velocity n i)
  signedGaussianSmooth : ∀ l n i, HarmonicResidual.SmoothCoefficients G.domain
    (((p).signedGaussianBlock v c u l).velocity n i)
  particularSolenoidal : ∀ l,
    HarmonicWaveInteraction.ModeSolenoidal (p).strip c ((p).particularBlock v c u l)
  signedSolenoidal : ∀ l,
    HarmonicWaveInteraction.ModeSolenoidal (p).strip c ((p).signedBlock v c u l)
  particularSupport : ∀ l, HarmonicSourceSupport.InputSupportOn G.domain (S l)
    ((p).particularBlock v c u l) ((p).particularGaussianBlock v c u l).velocity 0
  signedSupport : ∀ l, HarmonicSourceSupport.InputSupportOn G.domain (S l)
    ((p).signedBlock v c u l) ((p).signedGaussianBlock v c u l).velocity 0
  particularGaussian : ∀ β i j, LabelSumBounds.UniformClass (p).strip
    (fun _ _ z => Real.sqrt ((p).strip.zeta z)) β
    (fun l n z => ((p).particularGaussianBlock v c u l).velocity n i j z)
  signedGaussian : ∀ β i j, LabelSumBounds.UniformClass (p).strip
    (fun _ _ z => Real.sqrt ((p).strip.zeta z)) β
    (fun l n z => ((p).signedGaussianBlock v c u l).velocity n i j z)
  particularField : WaveStateRegularity.AngularSmooth G.domain ((p).particularVelocity v c u)
  signedField : WaveStateRegularity.AngularSmooth G.domain ((p).signedVelocity v c u)
  particularPressureField : ∀ n, ContDiffOn ℝ ∞ ((p).particularPressure v c u n)
    (G.domain ×ˢ (univ : Set ℝ))
  signedPressureField : ∀ n, ContDiffOn ℝ ∞ ((p).signedPressure v c u n)
    (G.domain ×ˢ (univ : Set ℝ))
  particularPeriodic : OscillationPeriodic G.region.carrier ((p).particularVelocity v c u)
  signedPeriodic : OscillationPeriodic G.region.carrier ((p).signedVelocity v c u)
  particularRadialSupport : WaveStateRegularity.WaveSupport G.region G.patch.a G.patch.b
    ((p).particularVelocity v c u)
  signedRadialSupport : WaveStateRegularity.WaveSupport G.region G.patch.a G.patch.b
    ((p).signedVelocity v c u)
  tangentField : WaveStateRegularity.AngularSmooth G.domain
    (LabelSumBounds.fieldSum (v).labels (fun l => ((p).signedTangent v c u l).oscillation))
  tangentPeriodic : OscillationPeriodic G.region.carrier
    (LabelSumBounds.fieldSum (v).labels (fun l => ((p).signedTangent v c u l).oscillation))
  tangentRadialSupport : WaveStateRegularity.WaveSupport G.region G.patch.a G.patch.b
    (LabelSumBounds.fieldSum (v).labels (fun l => ((p).signedTangent v c u l).oscillation))
  particularLinear : ∀ i j, j ≠ 0 → LabelSumBounds.UniformWaveClass (p).strip P (1+σ-3*κ)
    (fun l n z =>
      (HarmonicResidual.residualBlock c u ((v).blocks l) ((v).gaussian l) ((v).aliasCoefficients
          l)).velocity n i j z +
      (HarmonicWaveInteraction.linearGoodBlock c ((v).blocks l) ((p).particularBlock v c u l)
        ((p).particularGaussianBlock v c u l).velocity).velocity n i j z)
  signedLinear : UniformHarmonicInteraction.UniformVelocity (p).strip P (1+σ-4*κ)
    (fun l => HarmonicWaveInteraction.linearGoodBlock c ((p).beforeSignedBlock v c u l)
      ((p).signedBlock v c u l) ((p).signedGaussianBlock v c u l).velocity)

namespace WaveData

variable {ι : Type} {G : SignedMeanGain.Geometry} {p : CycleParameters ι}
    {v : CycleCoefficients ι} {c : Context Point} {u : State Point}
    {P : ι → ℕ → Point → ℝ} {S : ι → ℕ → Set Point} {σ κ : ℝ}
    (W : WaveData G p v c u P S σ κ)

include W

/-- The signed exact coefficient is its tangent coefficient plus the
literal curl difference. -/
theorem signed (hκ : κ ≤ 1 / 2) : ∀ i j,
    LabelSumBounds.UniformWaveClass (p).strip P (1/2+σ-κ)
      (fun l n z => ((p).signedBlock v c u l).velocity n i j z) := by
  intro i j
  apply ((W.tangent i j).add ((W.curl i j).mono_exponent (by linarith))).congr
  intro l n z hz
  change ((p).signedTangent v c u l).velocity n i j z +
      (((p).signedBlock v c u l).velocity n i j z - ((p).signedTangent v c u l).velocity n i j z) =
          _
  ring

theorem particular_zero_germ (hS : ∀ l n, IsClosed (S l n))
    (l : ι) (n : ℕ) {z : Point} (hz : z ∈ G.domain) (hn : z ∉ S l n)
    (i : Fin 3) (j : ℤ) (hj : j ≠ 0) :
    ((p).particularBlock v c u l).velocity n i j =ᶠ[𝓝 z] fun _ => 0 :=
  block_velocity_zero_germ_of_inputSupport G.domain_open (hS l) (W.particularSupport l)
    ((p).particularBlock_real v c u l).1 n hz hn i j hj

theorem signed_zero_germ (hS : ∀ l n, IsClosed (S l n))
    (l : ι) (n : ℕ) {z : Point} (hz : z ∈ G.domain) (hn : z ∉ S l n)
    (i : Fin 3) (j : ℤ) (hj : j ≠ 0) :
    ((p).signedBlock v c u l).velocity n i j =ᶠ[𝓝 z] fun _ => 0 :=
  block_velocity_zero_germ_of_inputSupport G.domain_open (hS l) (W.signedSupport l)
    ((p).signedBlock_real v c u l).1 n hz hn i j hj

/-- The two tensor regularity inputs are consequences of the actual
finite wave fields, their radial support and their torus periodicity. -/
theorem covariance_moving
    (hu : WaveStateRegularity.AngularSmooth G.domain (u).oscillation)
    (hup : OscillationPeriodic G.region.carrier (u).oscillation) :
    (∀ i j, GaugeMomentBalances.MovingField G.region G.patch.a G.patch.b
      (SignedMeanGain.covarianceIncrement (u).oscillation ((p).particularVelocity v c u) i j)) ∧
    (∀ i j, GaugeMomentBalances.MovingField G.region G.patch.a G.patch.b
      (SignedMeanGain.covarianceIncrement ((p).afterParticular v c u).oscillation
        ((p).signedVelocity v c u) i j)) := by
  refine ⟨covarianceIncrement_moving G.region hu W.particularField
    W.particularRadialSupport hup W.particularPeriodic, ?_⟩
  exact covarianceIncrement_moving G.region (hu.add W.particularField) W.signedField
    W.signedRadialSupport (hup.add W.particularPeriodic) W.signedPeriodic

end WaveData

/-- The fixed geometry and primitive operator data shared by every cycle.
The similarity data are identified with the same region, strip and gauge
used in the invariant, including the entire radial and free-torus fiber. -/
structure StaticData (G : SignedMeanGain.Geometry) (h : ℝ) (index : ℕ → ℕ)
    (axial : PressureStream.Plane × PressureStream.Plane) (r : RankData PressureStream.Plane)
    (c : Context Point) (κ : ℝ) where
  /-- Alias data of `StaticData`, of type `ActualCycleExcluded.SimilarityData`. -/
  aliasData : ActualCycleExcluded.SimilarityData
  coord : G.coord = 2 * aliasData.h
  region : HEq G.region aliasData.region
  inner : G.patch.a = aliasData.inner
  outer : G.patch.b = aliasData.outer
  gauge : G.gauge = aliasData.gauge
  strip : G.strip = aliasData.strip
  time : h = aliasData.h
  index_eq : index = aliasData.index
  operators_eq : c.operators = G.operators
  operators : OperatorBounds G.strip c.operators κ
  base : BaseBounds G.strip c.base
  axial_eq : axial = (G.axial, 0)
  temporal : c.operators.vT = (0, (0, TorusInverse.vector .temporal))
  fast : ∀ n, c.operators.fastCoefficient n = ChartScales.Tg ^ index n * ChartScales.Q n ^ (1+h)
  angular_slow : LocalRankDefect.IsSlowOn G.region.carrier c.base.angular
  axial_slow : LocalRankDefect.IsSlowOn G.region.carrier c.base.axial
  /-- Rank exponent of `StaticData`, of type `ℝ`. -/
  rankExponent : ℝ
  /-- Rank coefficient of `StaticData`, of type `ℝ`. -/
  rankCoefficient : ℝ
  rankParameters : RankStateBounds.NormalizedParameters G.coord rankExponent rankCoefficient r
      G.region.carrier
  rankCoefficient_ne : rankCoefficient ≠ 0
  rank_left : G.patch.a < r.inner
  rank_right : r.outer < G.patch.b

namespace StaticData

variable {G : SignedMeanGain.Geometry} {h : ℝ} {index : ℕ → ℕ}
    {axial : PressureStream.Plane × PressureStream.Plane} {r : RankData PressureStream.Plane}
    {c : Context Point} {κ : ℝ} (D : StaticData G h index axial r c κ)

include D

theorem radius_pos {z : Point} (hz : z ∈ G.strip.domain) : 0 < c.operators.radius z := by
  rw [D.operators_eq]
  exact G.strip_radius_pos hz

theorem graph : ∃ slowTime : PressureStream.Plane × PressureStream.Plane,
    ∃ temporal : PressureStream.Plane,
      c.operators = graphOperators G.gauge.radial c.operators.epsilon c.operators.fastCoefficient
        axial slowTime temporal := by
  refine ⟨(G.time,0), G.temporal, ?_⟩
  rw [D.operators_eq, D.axial_eq]
  rfl

theorem time_nonneg : 0 ≤ h := by
  rw [D.time]
  exact D.aliasData.h_pos.le

theorem slow_scale : ∀ n, ChartScales.S n ≤ G.slow n := by
  have hs : G.slow = D.aliasData.slow := congrArg (fun s : StripData Point => s.slow) D.strip
  rw [hs]
  exact D.aliasData.slow_scale

theorem index_lower : ∀ n, ChartScales.nativeIndex h n ≤ index n + D.aliasData.gap := by
  simpa only [D.time, D.index_eq] using D.aliasData.index_lower

theorem compatible {ι : Type} (particular : ι → ParticularParameters CycleSlow)
    (signed : ι → PeriodizedSignedParameters Point TorusInverse.Frequency) :
    ActualCycleExcluded.Compatible D.aliasData
      (CycleParameters.ofGeometry G h index axial particular signed r) c := by
  refine ⟨D.gauge, D.strip, D.time, D.index_eq, ?_, D.temporal⟩
  funext n
  simpa only [D.time, D.index_eq] using D.fast n

end StaticData

private theorem primitive_region_transport {coord coord' a b : ℝ}
    {U : SlowRegion coord} {V : SlowRegion coord'} {c : Context Point} {u : State Point}
    (hc : coord = coord') (hU : HEq U V)
    (H : MeanStateRegularity.PrimitiveData U a b c u) :
    MeanStateRegularity.PrimitiveData V a b c u := by
  subst coord'
  have hUV := eq_of_heq hU
  subst V
  exact H

private theorem moving_region_transport {coord coord' a b : ℝ}
    {U : SlowRegion coord} {V : SlowRegion coord'} {f : MeanIncrementBounds.Field Point}
    (hc : coord = coord') (hU : HEq U V)
    (H : GaugeMomentBalances.MovingField U a b f) :
    GaugeMomentBalances.MovingField V a b f := by
  subst coord'
  have hUV := eq_of_heq hU
  subst V
  exact H

private theorem region_carrier_eq {coord coord' : ℝ} {U : SlowRegion coord} {V : SlowRegion coord'}
    (hc : coord = coord') (hU : HEq U V) : U.carrier = V.carrier := by
  subst coord'
  have hUV := eq_of_heq hU
  subst V
  rfl

section Assemble

variable {ι : Type} (G : SignedMeanGain.Geometry)
    (h : ℝ) (index : ℕ → ℕ) (axial : PressureStream.Plane × PressureStream.Plane)
    (particular : ι → ParticularParameters CycleSlow)
    (signed : ι → PeriodizedSignedParameters Point TorusInverse.Frequency)
    (r : RankData PressureStream.Plane) (c : Context Point) (x : CycleState ι)
    (primary : ι → HarmonicBlock Point) (P : ι → ℕ → Point → ℝ)
    (S : ι → ℕ → Set Point) {σ κ : ℝ}

local notation "p" => CycleParameters.ofGeometry G h index axial particular signed r
local notation "v" => x.coefficients
local notation "u" => x.state

private theorem meanStepData
    (H : CycleAnalyticInvariant G c primary P S σ x)
    (W : WaveData G p v c u P S σ κ)
    (hPrimitive : MeanStateRegularity.PrimitiveData G.region G.gauge.radial.inner
      G.gauge.radial.outer c u)
    (hXPg : ∀ i j, GaugeMomentBalances.MovingField G.region G.gauge.radial.inner
      G.gauge.radial.outer (SignedMeanGain.covarianceIncrement (u).oscillation
        ((p).particularVelocity v c u) i j))
    (hXSg : ∀ i j, GaugeMomentBalances.MovingField G.region G.gauge.radial.inner
      G.gauge.radial.outer (SignedMeanGain.covarianceIncrement ((p).afterParticular v c
          u).oscillation
        ((p).signedVelocity v c u) i j))
    (hg : LocalRankDefect.RankGeometry G.gauge r G.region.carrier c u)
    (hgraph : ∃ slowTime : PressureStream.Plane × PressureStream.Plane,
      ∃ temporal : PressureStream.Plane,
        c.operators = graphOperators G.gauge.radial c.operators.epsilon c.operators.fastCoefficient
          axial slowTime temporal) : CycleMeanEquation.StepData G.region p v c u := {
    inner_pos := G.inner_pos
    exponent_pos := G.exponent_pos
    length := G.length_eq
    domain := fun z hz => ⟨G.strip_radius_pos hz, G.strip_subset hz⟩
    primitive := hPrimitive
    particular_covariance := hXPg
    signed_covariance := hXSg
    rank := hg
    operators := hgraph
    particular_regular := fun l => {
      phase := H.phase l
      velocity := fun n i j => (W.particularSmooth l n i j).mono G.strip_subset
      pressure := fun n j => (W.particularPressureSmooth l n j).mono G.strip_subset }
    signed_regular := fun l => {
      phase := by simp only [(W.carrier l).phase]; exact H.phase l
      velocity := fun n i j => (W.signedSmooth l n i j).mono G.strip_subset
      pressure := fun n j => (W.signedPressureSmooth l n j).mono G.strip_subset }
    particular_solenoidal := W.particularSolenoidal
    signed_solenoidal := W.signedSolenoidal
    angular := H.angular
    signed_carrier := W.carrier }

/-- Assemble the invariant after the quantitative mean calculation.
The public preservation theorem below derives those mean inputs from
the same finite waves and measured cross defects. -/
private theorem assemble
    (H : CycleAnalyticInvariant G c primary P S σ x)
    (W : WaveData G p v c u P S σ κ)
    (hσ : 1 / 5 ≤ σ) (hκsmall : κ ≤ 1 / 100000)
    (ho : OperatorBounds G.strip c.operators κ) (hb : BaseBounds G.strip c.base)
    (hR : ∀ z ∈ G.strip.domain, 0 < c.operators.radius z)
    (hS : ∀ l n, IsClosed (S l n)) {C : ℕ → ι → Set Point}
    (hSC : ∀ l n, S l n ⊆ C n l)
    (hNormal : ∀ i, LocalizedWaveBounds.LocalUnweighted G.strip C 0
      (fun n l z => HarmonicMeanInteraction.slowNormal c ho hR ((v).blocks l).phase n z i))
    (hFreq : LocalizedWaveBounds.LocalUnweighted G.strip C (-(1 / 2))
      (fun n l _ => ((v).blocks l).frequency n))
    (hAng : LocalizedWaveBounds.LocalUnweighted G.strip C (-(1 / 2))
      (fun n l _ => (((v).blocks l).angularFrequency n : ℝ)))
    (hP0 : ∀ l n z, z ∈ G.strip.domain → 0 ≤ P l n z)
    (hP1 : ∀ l n z, z ∈ G.strip.domain → P l n z ≤ 1)
    (hg : LocalRankDefect.RankGeometry G.gauge r G.region.carrier c u)
    (hrlength : ∀ n z, z ∈ G.region.carrier → r.length n z = qLength G.coord z)
    (hrleft : G.patch.a ≤ r.inner) (hrright : r.outer ≤ G.patch.b)
    (hgraph : ∃ slowTime : PressureStream.Plane × PressureStream.Plane,
      ∃ temporal : PressureStream.Plane,
        c.operators = graphOperators G.gauge.radial c.operators.epsilon c.operators.fastCoefficient
          axial slowTime temporal)
    (hCovP : SignedMeanGain.TensorClass G.strip (1 + σ)
      (SignedMeanGain.covarianceIncrement (u).oscillation ((p).particularVelocity v c u)))
    (hCovS : SignedMeanGain.TensorClass G.strip (1 + σ - κ)
      (SignedMeanGain.covarianceIncrement ((p).afterParticular v c u).oscillation
          ((p).signedVelocity v c u)))
    (hTemporal : IncrementBounds G.strip (1 + σ - 2 * κ) ((p).temporalIncrement v c u))
    (hRank : IncrementBounds G.strip (1 + σ - 2 * κ) ((p).rankIncrement v c u))
    (hCumulative : CorrectionState.CumulativeBounds G.strip ((p).next v c u))
    (hDebt : DefectBounds G.slowStrip (σ + 1 / 10) c ((p).next v c u))
    (hTheta : MeanClass G.strip (1 + (σ + 1 / 10)) (((p).next v c u).thetaResidual c))
    (hAxial : MeanClass G.strip (1 + (σ + 1 / 10))
      (((p).next v c u).axialResidual c - fun n z =>
        temporalAliasState G.gauge h index c ((p).afterSigned v c u) n (z, 0) 2))
    (hAxis : ∀ β, MeanClass G.strip β ((p).nextAxisymmetricAlias v c u x.axisymmetricAlias)) :
    CycleAnalyticInvariant G c primary P S (σ+1/10) (CycleState.step p c x) := by
  have hsigned := W.signed (show κ ≤ 1/2 by linarith)
  have hzpart n l z (hz : z ∈ G.strip.domain) (hn : z ∉ C n l) i j hj :=
    W.particular_zero_germ hS l n (G.strip_subset hz) (fun hmem => hn (hSC l n hmem)) i j hj
  have hzsigned n l z (hz : z ∈ G.strip.domain) (hn : z ∉ C n l) i j hj :=
    W.signed_zero_germ hS l n (G.strip_subset hz) (fun hmem => hn (hSC l n hmem)) i j hj
  have hNewSupport := (p).next_inputSupport v c u H.inputSupport W.particularSupport W.signedSupport
  have hNewReal := (p).next_realCoefficients v c u H.realCoefficients
  have hzfinal n l z (hz : z ∈ G.strip.domain) (hn : z ∉ C n l) i j hj :=
    velocity_zero_germ_of_inputSupport G.domain_open hS hNewSupport hNewReal l n
      (G.strip_subset hz) (fun hmem => hn (hSC l n hmem)) i j hj
  obtain ⟨hAfter, hSolenoidal⟩ := (p).waveStages_residual_gain v c u hσ hκsmall ho hR hb
    H.cumulative.velocity W.carrier H.wave W.particular hsigned
    (fun l n j => (H.pressureCoefficientSmooth l n j).mono G.strip_subset)
    (fun l n j => (W.particularPressureSmooth l n j).mono G.strip_subset)
    (fun l n j => (W.signedPressureSmooth l n j).mono G.strip_subset)
    H.zeroVelocity H.bands.velocityPressure H.phase H.frequency H.angular H.solenoidal
    W.particularSolenoidal W.signedSolenoidal hNormal hFreq hAng hzpart hzsigned hP0 hP1
    W.particularLinear W.signedLinear
  obtain ⟨hWave, hDifference⟩ := (p).finalBlock_uniform_cumulative v c u primary hσ hκsmall
    H.wave H.difference W.particular hsigned
  have hResidual := (p).meanStages_residual_gain v c u hκsmall ho hR hb.smooth
    H.cumulative.velocity.smooth hTemporal hRank (fun i j _ => hWave i j)
    hNormal hFreq hAng hzfinal hAfter
  have hPressure := (p).finalBlock_pressure_cumulative v c u hσ hκsmall
    H.pressure W.particularPressure W.signedPressure
  obtain ⟨hXP, hXS⟩ := W.covariance_moving H.oscillationSmooth H.oscillationPeriodic
  have hPrimitive : MeanStateRegularity.PrimitiveData G.region G.gauge.radial.inner
      G.gauge.radial.outer c u := by
    simpa only [G.inner_eq, G.outer_eq] using H.primitives
  have hXPg : ∀ i j, GaugeMomentBalances.MovingField G.region G.gauge.radial.inner
      G.gauge.radial.outer (SignedMeanGain.covarianceIncrement (u).oscillation
        ((p).particularVelocity v c u) i j) := by
    simpa only [G.inner_eq, G.outer_eq] using hXP
  have hXSg : ∀ i j, GaugeMomentBalances.MovingField G.region G.gauge.radial.inner
      G.gauge.radial.outer (SignedMeanGain.covarianceIncrement ((p).afterParticular v c
          u).oscillation
        ((p).signedVelocity v c u) i j) := by
    simpa only [G.inner_eq, G.outer_eq] using hXS
  have hpr := (p).next_primitive v c u G.region G.inner_pos G.exponent_pos G.length_eq
    hPrimitive hXPg hXSg hg
  have hmass := (p).next_zeroMassesOn v c u G.region G.inner_pos G.exponent_pos G.length_eq
    hPrimitive hXPg hXSg hg hrlength
    (by change G.gauge.radial.inner ≤ r.inner; rw [G.inner_eq]; exact hrleft)
    (by change r.outer ≤ G.gauge.radial.outer; rw [G.outer_eq]; exact hrright) H.masses
  have hStep := meanStepData G h index axial particular signed r c x primary P S H W
    hPrimitive hXPg hXSg hg hgraph
  have hAlias := H.representation.alias_eq_lift H.aliasCoefficients
  have hAliasContinuous : AngularContinuous (u).errors.aliasError := by
    rw [hAlias]
    intro n z i
    change Continuous (fun _ : ℝ => x.axisymmetricAlias n z i)
    exact continuous_const
  have hAliasMean : angularMeanVector (u).errors.aliasError = x.axisymmetricAlias := by
    rw [hAlias]
    funext n z i
    exact congrFun (congrFun (angularAverage_axisymmetric (fun n z => x.axisymmetricAlias n z i))
        n) z
  have hGaussianMeans (i : Fin 3) : MeanClass G.strip (1+(σ+1/10))
      (fun n z => angularMeanVector (u).errors.gaussian n z i) := by
    rw [H.gaussianMean]
    exact MemClass.zero (fun _ z hz => G.strip.zeta_nonneg z hz)
  have hAliasMeans (i : Fin 3) : MeanClass G.strip (1+(σ+1/10))
      (fun n z => angularMeanVector (u).errors.aliasError n z i) := by
    rw [hAliasMean]
    exact (H.axisFlat _).map (ContinuousLinearMap.proj i)
  have hMean := (p).next_meanResidualBounds v c u H.angular W.carrier
    (fun n z hz i => H.baseAngular n z (G.strip_subset hz) i)
    H.representation.gaussian_angularContinuous hAliasContinuous hTheta hAxial
    (hGaussianMeans 1) (hGaussianMeans 2) (hAliasMeans 1) (hAliasMeans 2)
  refine {
    representation := (p).next_representation v c u H.representation W.carrier
    bands := (p).next_coefficient_bands v c u H.bands
    realCoefficients := hNewReal
    inputSupport := hNewSupport
    sourceBand := (p).next_residual_band v c u H.bands
    zeroVelocity := (p).finalBlock_zero v c u H.zeroVelocity
    zeroPressure := (p).finalBlock_pressure_zero v c u H.zeroPressure
    carrier := fun l => ⟨(H.carrier l).frequency, (H.carrier l).phase, (H.carrier l).angular⟩
    phase := H.phase
    frequency := H.frequency
    angular := H.angular
    coefficientSmooth := fun l n i j =>
      ((H.coefficientSmooth l n i j).add (W.particularSmooth l n i j)).add (W.signedSmooth l n i j)
    pressureCoefficientSmooth := fun l n j =>
      ((H.pressureCoefficientSmooth l n j).add (W.particularPressureSmooth l n j)).add
        (W.signedPressureSmooth l n j)
    gaussianCoefficientSmooth := fun l n i j =>
      ((H.gaussianCoefficientSmooth l n i j).add (W.particularGaussianSmooth l n i j)).add
        (W.signedGaussianSmooth l n i j)
    solenoidal := hSolenoidal
    wave := hWave
    pressure := hPressure
    difference := hDifference
    cumulative := hCumulative
    covariance := (p).next_covariance_mem v c u (by linarith : (1:ℝ) ≤ 1+σ)
      (by linarith : (1:ℝ) ≤ 1+σ-κ) H.covariance hCovP hCovS
    residual := hResidual
    mean := hMean
    meanHypotheses := hStep.next_meanHypotheses H.meanHypotheses
    debt := hDebt
    primitives := ?_
    reconstructed := hpr.2
    masses := hmass
    oscillationSmooth := (p).next_oscillation_smooth v c u H.oscillationSmooth W.particularField
        W.signedField
    oscillatoryPressureSmooth := ?_
    oscillationPeriodic := (p).next_oscillation_periodic v c u H.oscillationPeriodic
      W.particularPeriodic W.signedPeriodic
    oscillationSupport := (p).next_oscillation_support v c u H.oscillationSupport
      W.particularRadialSupport W.signedRadialSupport
    gaussianFlat := fun β => (p).next_gaussian_mem v c u (H.gaussianFlat β)
      (W.particularGaussian β) (W.signedGaussian β)
    gaussianMean := ?_
    aliasCoefficients := H.aliasCoefficients
    axisFlat := hAxis
    baseAngular := ?_ }
  · have hpn := hpr.1
    change MeanStateRegularity.PrimitiveData G.region G.gauge.radial.inner G.gauge.radial.outer
      c ((p).next v c u) at hpn
    simp only [G.inner_eq, G.outer_eq] at hpn
    exact hpn
  · intro n
    change ContDiffOn ℝ ∞ (((p).next v c u).oscillatoryPressure n) _
    rw [(p).next_oscillatoryPressure]
    exact ((H.oscillatoryPressureSmooth n).add (W.particularPressureField n)).add
        (W.signedPressureField n)
  · exact ((p).next_gaussian_angularMean v c u H.angular W.carrier
      H.representation.gaussian_angularContinuous).trans H.gaussianMean
  · intro n z hz i
    change Continuous (fun θ => ((p).next v c u).errors.base n (z,θ) i)
    rw [(p).next_base_error]
    exact H.baseAngular n z hz i

end Assemble

section Preservation

variable {ι : Type} (G : SignedMeanGain.Geometry)
    (h : ℝ) (index : ℕ → ℕ) (axial : PressureStream.Plane × PressureStream.Plane)
    (particular : ι → ParticularParameters CycleSlow)
    (signed : ι → PeriodizedSignedParameters Point TorusInverse.Frequency)
    (r : RankData PressureStream.Plane) (c : Context Point) (x : CycleState ι)
    (primary : ι → HarmonicBlock Point) (P : ι → ℕ → Point → ℝ)
    (S : ι → ℕ → Set Point) {σ κ : ℝ}

local notation "p" => CycleParameters.ofGeometry G h index axial particular signed r
local notation "v" => x.coefficients
local notation "u" => x.state

/-- The remaining inputs to one cycle are on its actual native waves and
their fixed geometric assembly.  The only leading-covariance identity is
on a fixed tail; the finite head is retained by the proof. -/
structure StepData (D : StaticData G h index axial r c κ)
    (H : CycleAnalyticInvariant G c primary P S σ x) (hσ : 1 / 5 ≤ σ) where
  waves : WaveData G p v c u P S σ κ
  /-- Primary band of `StepData`, of type `ℕ`. -/
  primaryBand : ℕ
  primary_band : ∀ l, (primary l).BandLimited primaryBand
  envelope_nonneg : ∀ l n z, z ∈ G.strip.domain → 0 ≤ P l n z
  envelope_le_one : ∀ l n z, z ∈ G.strip.domain → P l n z ≤ 1
  /-- Cells of `StepData`, of type `ℕ → ι → Set Point`. -/
  cells : ℕ → ι → Set Point
  carrier_closed : ∀ l n, IsClosed (S l n)
  carrier_cells : ∀ l n, S l n ⊆ cells n l
  normal : ∀ i, LocalizedWaveBounds.LocalUnweighted G.strip cells 0
    (fun n l z => HarmonicMeanInteraction.slowNormal c D.operators
      (fun _ hz => D.radius_pos hz) ((v).blocks l).phase n z i)
  frequency : LocalizedWaveBounds.LocalUnweighted G.strip cells (-(1/2))
    (fun n l _ => ((v).blocks l).frequency n)
  angular : LocalizedWaveBounds.LocalUnweighted G.strip cells (-(1/2))
    (fun n l _ => (((v).blocks l).angularFrequency n : ℝ))
  /-- Assembly supplied by `StepData`. -/
  assembly : SignedMeanGain.Assembly
    ((p).signedFamily v c u primary P hσ primaryBand primary_band H.bands H.carrier waves.carrier
      H.wave H.difference waves.particular waves.tangent waves.curl
      envelope_nonneg envelope_le_one H.angular)
  labels : assembly.labels = (v).labels
  old_support : LabelSumBounds.SupportedOscillations assembly.slots assembly.label assembly.window
    assembly.auxiliary G.strip.domain (fun l => ((v).blocks l).oscillation)
  particular_support : LabelSumBounds.SupportedOscillations assembly.slots assembly.label
      assembly.window
    assembly.auxiliary G.strip.domain (fun l => ((p).particularBlock v c u l).oscillation)
  primary_smooth : WaveStateRegularity.AngularSmooth G.domain (SignedMeanGain.primaryField _
      assembly)
  primary_periodic : OscillationPeriodic G.region.carrier (SignedMeanGain.primaryField _ assembly)
  rank_geometry : LocalRankDefect.RankGeometry G.gauge r G.region.carrier c u
  /-- Tail start of `StepData`, of type `ℕ`. -/
  tailStart : ℕ
  cross_tail : ∀ n, tailStart ≤ n → ∀ z ∈ G.strip.domain, ∀ i : Fin 2,
    StateMomentBalances.meanBar (SignedMeanGain.crossTensor _ assembly 0 i.succ) n z =
      LocalSignedRequest.requestedStress G.patch G.coord c ((p).afterParticular v c u) n z i

/-- In addition to preservation, keep the actual increments needed by
the physical-stage estimates. -/
structure StepResult : Prop where
  invariant : CycleAnalyticInvariant G c primary P S (σ+1/10) (CycleState.step p c x)
  temporal : IncrementBounds G.strip (1+σ-2*κ) ((p).temporalIncrement v c u)
  rank : IncrementBounds G.strip (1+σ-2*κ) ((p).rankIncrement v c u)
  pressure : MeanClass G.strip (1+σ-2*κ) (((p).next v c u).pressure - (u).pressure)
  velocityCoefficients : ∀ i j, LabelSumBounds.UniformWaveClass G.strip P (1/2+σ-κ)
    (fun l n z => ((p).finalBlock v c u l).velocity n i j z - ((v).blocks l).velocity n i j z)
  pressureCoefficients : ∀ j, LabelSumBounds.UniformWaveClass G.strip P (1+σ-κ)
    (fun l n z => ((p).finalBlock v c u l).pressure n j z - ((v).blocks l).pressure n j z)
  afterSignedTheta : MeanClass G.strip (1+σ-2*κ) (((p).afterSigned v c u).thetaResidual c)
  afterSignedAxial : MeanClass G.strip (1+σ-2*κ) (((p).afterSigned v c u).axialResidual c)

/-- The complete analytic step, with actual covariance estimates,
finite-head cross defects, temporal/rank reconstruction, and all error
bookkeeping derived in the proof. -/
theorem step (D : StaticData G h index axial r c κ)
    (H : CycleAnalyticInvariant G c primary P S σ x)
    (hσ : 1 / 5 ≤ σ) (hκsmall : κ ≤ 1 / 100000)
    (d : StepData G h index axial particular signed r c x primary P S D H hσ) :
    StepResult G h index axial particular signed r c x primary P S (σ := σ) (κ := κ) := by
  let W := d.waves
  let F := (p).signedFamily v c u primary P hσ d.primaryBand d.primary_band H.bands H.carrier
    W.carrier H.wave H.difference W.particular W.tangent W.curl d.envelope_nonneg d.envelope_le_one
        H.angular
  let a : SignedMeanGain.Assembly F := d.assembly
  have halabels : a.labels = (v).labels := d.labels
  have hκ : 0 ≤ κ := D.operators.kappa_nonneg
  have hfixed : (reconstructState G.gauge c u).pressure = (u).pressure :=
    congrArg (fun z : State Point => z.pressure) H.reconstructed
  have hrep₀ : (u).oscillation = LabelSumBounds.fieldSum a.labels (fun l => ((v).blocks
      l).oscillation) := by
    rw [halabels]
    funext n z i
    exact H.representation.velocity n z i
  have hCov₀ := assembledCovarianceIncrement_mem (show (1:ℝ)/2 ≤ 1/2+σ by linarith)
    a.labels a.label a.injective a.level a.window a.window_continuous a.auxiliary
    (v).blocks ((p).particularBlock v c u) (v).residualBand H.bands.velocityPressure
    ((p).particularBlock_band v c u) (fun _ => ⟨rfl,rfl,rfl⟩)
    (fun i j _ => H.wave i j) (fun i j _ => W.particular i j)
    H.zeroVelocity ((p).particularBlock_zero v c u) d.envelope_nonneg d.envelope_le_one H.angular
    d.old_support d.particular_support u hrep₀
  have hCovP : SignedMeanGain.TensorClass G.strip (1+σ)
      (SignedMeanGain.covarianceIncrement (u).oscillation ((p).particularVelocity v c u)) := by
    simp only [halabels, CycleParameters.particularVelocity,
      show (1:ℝ)/2+(1/2+σ) = 1+σ by ring] at hCov₀ ⊢
    exact hCov₀
  have hrep₁ : ((p).afterParticular v c u).oscillation = SignedMeanGain.oldField F a := by
    simpa only [SignedMeanGain.oldField, halabels, F, CycleParameters.signedFamily] using
      (p).beforeSignedBlock_represents v c u H.representation
  have hw₂ : SignedMeanGain.tangentField F a + SignedMeanGain.curlField F a =
      (p).signedVelocity v c u := by
    simpa only [SignedMeanGain.tangentField, SignedMeanGain.curlField, F,
      CycleParameters.signedFamily, halabels] using ((p).signedVelocity_split v c u).symm
  have hCovS : SignedMeanGain.TensorClass G.strip (1+σ-κ)
      (SignedMeanGain.covarianceIncrement ((p).afterParticular v c u).oscillation
        ((p).signedVelocity v c u)) := by
    have hh := (SignedMeanGain.signed_tensor_bounds hσ hκsmall F a).1
    rwa [SignedMeanGain.incrementTensor, ← hrep₁, hw₂] at hh
  obtain ⟨hXP, hXS⟩ := W.covariance_moving H.oscillationSmooth H.oscillationPeriodic
  have hXSFamily : ∀ i j, SignedMeanGain.MovingField G (SignedMeanGain.incrementTensor F a i j) :=
      by
    intro i j
    rw [SignedMeanGain.incrementTensor, ← hrep₁, hw₂]
    exact hXS i j
  have hTangent : WaveStateRegularity.AngularSmooth G.domain (SignedMeanGain.tangentField F a) := by
    simpa only [SignedMeanGain.tangentField, F, CycleParameters.signedFamily, halabels] using
        W.tangentField
  have hTangentPer : OscillationPeriodic G.region.carrier (SignedMeanGain.tangentField F a) := by
    simpa only [SignedMeanGain.tangentField, F, CycleParameters.signedFamily, halabels] using
        W.tangentPeriodic
  have hTangentSupport : WaveStateRegularity.WaveSupport G.region G.patch.a G.patch.b
      (SignedMeanGain.tangentField F a) := by
    simpa only [SignedMeanGain.tangentField, F, CycleParameters.signedFamily, halabels] using
        W.tangentRadialSupport
  have hCross : ∀ i j, SignedMeanGain.MovingField G (SignedMeanGain.crossTensor F a i j) :=
    symmetricCovariance_moving G.region d.primary_smooth hTangent hTangentSupport
        d.primary_periodic hTangentPer
  obtain ⟨hθ, hz⟩ := H.raw_mean_bounds
  obtain ⟨_, _, hθ₁, hz₁, _, _⟩ := waveStage_mean_gain G c u ((p).particularVelocity v c u)
    ((p).particularPressure v c u) ((p).particularGaussian v c u) hσ hκ hκsmall H.primitives
    D.operators D.base H.cumulative hfixed hθ hz H.debt hXP hCovP
  have H₁ := H.primitives.waveStage G.gauge ((p).particularVelocity v c u)
    ((p).particularPressure v c u) ((p).particularGaussian v c u) hXP
  have hDefects := SignedCrossDefectClass.residual_defects_all_exponents_of_primitive G c
    ((p).afterParticular v c u) F a hCross H₁ rfl hθ₁ hz₁ d.tailStart d.cross_tail
  have H₂ := H₁.waveStage G.gauge ((p).signedVelocity v c u)
    ((p).signedPressure v c u) ((p).signedGaussian v c u) hXS
  have H₂g : MeanStateRegularity.PrimitiveData G.region G.gauge.radial.inner G.gauge.radial.outer
      c ((p).afterSigned v c u) := by
    simp only [G.inner_eq, G.outer_eq] at H₂ ⊢
    exact H₂
  have HT := MeanStageRegularity.temporalStage_primitive H₂g G.inner_pos G.exponent_pos G.length_eq
    rfl h index axial
  have HG := MeanStageRegularity.rankGeometry_for_state HT G.inner_pos
      G.gauge.radial.inner_lt_outer d.rank_geometry
  have hMean := CrossBasedMeanComposition.CycleParameters.mean_gain_from_waves_of_cross_defects
    G h index axial particular signed r v c u primary P hσ d.primaryBand d.primary_band H.bands
    H.carrier W.carrier H.wave H.difference W.particular W.tangent W.curl
    d.envelope_nonneg d.envelope_le_one H.angular a halabels H.representation H.zeroVelocity
    ((p).particularBlock_zero v c u) d.old_support d.particular_support hκ hκsmall H.primitives
    D.operators_eq (by simpa only [D.operators_eq] using D.operators) D.base H.cumulative hfixed
    (fun n z hz => (H.masses n z hz).1) (fun n z hz => (H.masses n z hz).2)
    hθ hz H.debt hXP hXSFamily hCross (hDefects (1+σ+17/100+κ)).1 (hDefects (1+σ+17/100+κ)).2
    D.time_nonneg D.slow_scale D.aliasData.gap D.index_lower D.temporal D.fast
    D.angular_slow D.axial_slow HG D.rankParameters D.rankCoefficient_ne D.rank_left D.rank_right
  obtain ⟨hSθ, hSz, _, hT, hRank, hPressure, hCumulative, hDebt, hTheta, hAxial⟩ := hMean
  have HAlias : MeanStateRegularity.PrimitiveData D.aliasData.region D.aliasData.inner
      D.aliasData.outer c u := by
    simpa only [D.inner, D.outer] using primitive_region_transport D.coord D.region H.primitives
  have hXPAlias : ∀ i j, GaugeMomentBalances.MovingField D.aliasData.region D.aliasData.inner
      D.aliasData.outer
      (SignedMeanGain.covarianceIncrement (u).oscillation ((p).particularVelocity v c u) i j) := by
    intro i j
    simpa only [D.inner, D.outer] using moving_region_transport D.coord D.region (hXP i j)
  have hXSAlias : ∀ i j, GaugeMomentBalances.MovingField D.aliasData.region D.aliasData.inner
      D.aliasData.outer
      (SignedMeanGain.covarianceIncrement ((p).afterParticular v c u).oscillation
          ((p).signedVelocity v c u) i j) := by
    intro i j
    simpa only [D.inner, D.outer] using moving_region_transport D.coord D.region (hXS i j)
  have hRankAlias : LocalRankDefect.RankGeometry G.gauge r D.aliasData.region.carrier c u := by
    simpa only [region_carrier_eq D.coord D.region] using d.rank_geometry
  have hAxis := ActualCycleExcluded.nextAxisymmetricAlias_all_powers D.aliasData p v c u
    (D.compatible particular signed) HAlias hXPAlias hXSAlias hRankAlias D.operators D.base
    H.cumulative hCumulative H.covariance
    (fun i j => (hCovP i j).mono_exponent (show (1:ℝ) ≤ 1+σ by linarith))
    (fun i j => (hCovS i j).mono_exponent (show (1:ℝ) ≤ 1+σ-κ by linarith))
    hSz x.axisymmetricAlias H.axisFlat
  have hFull := assemble G h index axial particular signed r c x primary P S H W hσ hκsmall
    D.operators D.base (fun _ hz => D.radius_pos hz) d.carrier_closed d.carrier_cells
    d.normal d.frequency d.angular d.envelope_nonneg d.envelope_le_one d.rank_geometry
    D.rankParameters.length D.rank_left.le D.rank_right.le D.graph
    hCovP hCovS hT hRank hCumulative hDebt hTheta hAxial hAxis
  have hInc := (p).finalBlock_increment_bounds v c u hκ W.particular (W.signed (by linarith))
    W.particularPressure W.signedPressure
  exact ⟨hFull, hT, hRank, hPressure, hInc.1, hInc.2, hSθ, hSz⟩

/-- Projection of the complete step estimate to the stored invariant. -/
theorem step_preserves (D : StaticData G h index axial r c κ)
    (H : CycleAnalyticInvariant G c primary P S σ x)
    (hσ : 1 / 5 ≤ σ) (hκsmall : κ ≤ 1 / 100000)
    (d : StepData G h index axial particular signed r c x primary P S D H hσ) :
    CycleAnalyticInvariant G c primary P S (σ+1/10) (CycleState.step p c x) :=
  (step G h index axial particular signed r c x primary P S D H hσ hκsmall d).invariant

end Preservation

section Iteration

variable {ι : Type} (G : SignedMeanGain.Geometry)
    (h : ℝ) (index : ℕ → ℕ) (axial : PressureStream.Plane × PressureStream.Plane)
    (particular : ι → ParticularParameters CycleSlow)
    (signed : ι → PeriodizedSignedParameters Point TorusInverse.Frequency)
    (r : RankData PressureStream.Plane) (c : Context Point) (seed : CycleState ι)
    (primary : ι → HarmonicBlock Point) (P : ι → ℕ → Point → ℝ)
    (S : ι → ℕ → Set Point) {κ : ℝ}

local notation "p" => CycleParameters.ofGeometry G h index axial particular signed r
local notation "state" => CycleState.iterate (fun _ => p) c seed

/-- All stages use the same primitive parameters, strip, gauge, carriers,
and comparison primary.  The supplied data construct each actual wave;
they do not assume preservation of the invariant. -/
theorem iterate_invariant (D : StaticData G h index axial r c κ)
    (σ : ℕ → ℝ) (hσ : ∀ n, 1 / 5 ≤ σ n) (hσstep : ∀ n, σ (n + 1) = σ n + 1 / 10)
    (hκsmall : κ ≤ 1 / 100000)
    (hseed : CycleAnalyticInvariant G c primary P S (σ 0) seed)
    (data : ∀ n (H : CycleAnalyticInvariant G c primary P S (σ n) (state n)),
      StepData G h index axial particular signed r c (state n) primary P S D H (hσ n)) :
    ∀ n, CycleAnalyticInvariant G c primary P S (σ n) (state n) := by
  intro n
  induction n with
  | zero => exact hseed
  | succ n ih =>
    have hn := step_preserves G h index axial particular signed r c (state n) primary P S
      D ih (hσ n) hκsmall (data n ih)
    simpa only [CycleState.iterate_succ, hσstep] using hn

/-- The same induction also retains the actual increment estimates for
each positive physical stage. -/
theorem iterate_results (D : StaticData G h index axial r c κ)
    (σ : ℕ → ℝ) (hσ : ∀ n, 1 / 5 ≤ σ n) (hσstep : ∀ n, σ (n + 1) = σ n + 1 / 10)
    (hκsmall : κ ≤ 1 / 100000)
    (hseed : CycleAnalyticInvariant G c primary P S (σ 0) seed)
    (data : ∀ n (H : CycleAnalyticInvariant G c primary P S (σ n) (state n)),
      StepData G h index axial particular signed r c (state n) primary P S D H (hσ n)) :
    (∀ n, CycleAnalyticInvariant G c primary P S (σ n) (state n)) ∧
    ∀ n, StepResult G h index axial particular signed r c (state n) primary P S
      (σ := σ n) (κ := κ) := by
  have hi := iterate_invariant G h index axial particular signed r c seed primary P S
    D σ hσ hσstep hκsmall hseed data
  exact ⟨hi, fun n => step G h index axial particular signed r c (state n) primary P S
    D (hi n) (hσ n) hκsmall (data n (hi n))⟩

end Iteration

end NavierStokes.CorrectionAnalyticStep

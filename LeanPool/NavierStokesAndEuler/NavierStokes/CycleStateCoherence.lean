/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectionStep
public import LeanPool.NavierStokesAndEuler.NavierStokes.TemporalStateCoherence
public import LeanPool.NavierStokesAndEuler.NavierStokes.RankStateCoherence
import LeanPool.NavierStokesAndEuler.NavierStokes.MeanStageRegularity

/-!
# Full-fiber coherence through the actual correction recurrence

All comparisons below retain every radial, free auxiliary and angular
variable. Pressure reconstruction, the temporal inverse and the rank repair
are the literal operations in `CorrectionStep.CycleState.step`.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.CycleStateCoherence

open Set Function Filter CorrectionState CorrectionStep MeanIncrementBounds
open PhysicalResidualNaturality GaugeStateCoherence
open scoped Topology ContDiff BigOperators

/-- Plane: an abbreviation for `PressureStream.Plane`. -/
abbrev Plane := PressureStream.Plane
/-- Point: an abbreviation for `CorrectionStep.CyclePoint`. -/
abbrev Point := CorrectionStep.CyclePoint

/-- Fixed physical geometry of the recurrence. The radial exponent, gauge
and normalized rank coefficients are constructed from these parameters. -/
structure Geometry where
  /-- Step-size parameter of `Geometry`, of type `ℝ`. -/
  h : ℝ
  /-- Inner of `Geometry`, of type `ℝ`. -/
  inner : ℝ
  /-- Outer of `Geometry`, of type `ℝ`. -/
  outer : ℝ
  /-- Frequency of `Geometry`, of type `ℝ`. -/
  frequency : ℝ
  /-- Rank amplitude of `Geometry`, of type `ℝ`. -/
  rankAmplitude : ℝ
  /-- Rank shape of `Geometry`, of type `ℝ`. -/
  rankShape : ℝ
  /-- Rank inner of `Geometry`, of type `ℝ`. -/
  rankInner : ℝ
  /-- Rank outer of `Geometry`, of type `ℝ`. -/
  rankOuter : ℝ
  /-- Operator inner of `Geometry`, of type `ℝ`. -/
  operatorInner : ℝ
  /-- Operator outer of `Geometry`, of type `ℝ`. -/
  operatorOuter : ℝ
  /-- Index of `Geometry`, of type `ℕ → ℕ`. -/
  index : ℕ → ℕ
  h_pos : 0 < h
  h_lt_half : h < 1 / 2
  inner_pos : 0 < inner
  inner_lt_outer : inner < outer
  operator_lt : operatorInner < operatorOuter

/-- Gauge, given by `VariableGaugeMean.similarityGauge G.h (ChartScales.radialExponent G.h)
G.inner G.outer G.frequency G.inner_lt_outer G.index`. -/
noncomputable def Geometry.gauge (G : Geometry) : VariableGaugeMean.GaugeData Plane :=
  VariableGaugeMean.similarityGauge G.h (ChartScales.radialExponent G.h)
    G.inner G.outer G.frequency G.inner_lt_outer G.index

/-- Rank, given by `RankStateBounds.normalizedData (2 * G.h) (CoordinateAlgebra.A G.h)
G.rankAmplitude G.rankShape G.rankInner G.rankOuter`. -/
noncomputable def Geometry.rank (G : Geometry) : CorrectionState.RankData Plane :=
  RankStateBounds.normalizedData (2 * G.h) (CoordinateAlgebra.A G.h)
    G.rankAmplitude G.rankShape G.rankInner G.rankOuter

/-- Operators, given by `CommonBaseContext.operators G.h G.index G.operatorInner G.operatorOuter
G.operator_lt`. -/
noncomputable def Geometry.operators (G : Geometry) : MeanIncrementBounds.Operators Point :=
  CommonBaseContext.operators G.h G.index G.operatorInner G.operatorOuter G.operator_lt

/-- Identifications of primitive data, not conclusions about a state. -/
structure Realizes {ι : Type} (G : Geometry) (p : CycleParameters ι) (c : Context Point) : Prop
    where
  gauge : p.gauge = G.gauge
  rank : p.rank = G.rank
  timeExponent : p.timeExponent = G.h
  index : p.commonIndex = G.index
  axial : p.axial = ((0, 1), 0)
  operators : c.operators = G.operators

/-- State band, given by `StateOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv G.h n m k)
(bandVelocityScale G.h n m) (bandScale n m) u u n m`. -/
def StateBand (G : Geometry) (V : Set Plane) (n m k : ℕ) (u : State Point) : Prop :=
  StateOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv G.h n m k)
    (bandVelocityScale G.h n m) (bandScale n m) u u n m

/-- Context band, given by `ContextOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv G.h n m
k) (bandVelocityScale G.h n m) (bandScale n m) c c n m`. -/
def ContextBand (G : Geometry) (V : Set Plane) (n m k : ℕ) (c : Context Point) : Prop :=
  ContextOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv G.h n m k)
    (bandVelocityScale G.h n m) (bandScale n m) c c n m

/-- Axis band as an element of `Prop`. -/
def AxisBand (G : Geometry) (V : Set Plane) (n m k : ℕ) (a : AxisymmetricAlias) : Prop :=
  ∀ x ∈ PhysicalMeanDomain.slowDomain V, ∀ i,
    a n x i = (bandVelocityScale G.h n m * bandVelocityScale G.h n m * bandScale n m) *
      a m (bandChartEquiv G.h n m k x) i

/-! ## Finite label sums without equality of the two active sets -/

theorem sum_eq_mul_sum_of_support {ι : Type*} (s t : Finset ι) (a : ℝ)
    (f g : ι → ℝ) (hf : ∀ i, i ∉ s → f i = 0) (hg : ∀ i, i ∉ t → g i = 0)
    (he : ∀ i, f i = a * g i) : (∑ i ∈ s, f i) = a * ∑ i ∈ t, g i := by
  classical
  have hs : (∑ i ∈ s, f i) = ∑ i ∈ s ∪ t, f i := by
    exact Finset.sum_subset (Finset.subset_union_left) (fun i _ hi => hf i hi)
  have ht : (∑ i ∈ t, g i) = ∑ i ∈ s ∪ t, g i := by
    exact Finset.sum_subset (Finset.subset_union_right) (fun i _ hi => hg i hi)
  rw [hs, ht, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => he i)

/-- Primitive wave transport with the velocity, pressure and excluded
Gaussian terms in their respective physical units. -/
structure WaveOn {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set D) (e : D ≃L[ℝ] E) (c l : ℝ)
    (w : Oscillation D) (p : OscillatoryScalar D) (g : Oscillation D)
    (wr : Oscillation E) (pr : OscillatoryScalar E) (gr : Oscillation E) (n m : ℕ) : Prop where
  velocity : ∀ x ∈ U, ∀ theta i, w n (x, theta) i = c * wr m (e x, theta) i
  pressure : ∀ x ∈ U, ∀ theta, p n (x, theta) = (c*c) * pr m (e x, theta)
  gaussian : ∀ x ∈ U, ∀ theta i, g n (x, theta) i = (c*c*l) * gr m (e x, theta) i

/-- The support hypotheses concern each omitted label, so different active
sets in neighboring bands are permitted. -/
structure LabelWavesOn {ι : Type} (U : Set Point) (e : Point ≃L[ℝ] Point) (c l : ℝ)
    (labels : ℕ → Finset ι) (b g : ι → HarmonicBlock Point) (n m : ℕ) : Prop where
  wave : ∀ i, WaveOn U e c l (b i).oscillation (b i).oscillatoryPressure (g i).oscillation
    (b i).oscillation (b i).oscillatoryPressure (g i).oscillation n m
  left_zero : ∀ i, i ∉ labels n → ∀ x ∈ U, ∀ theta,
    (b i).oscillation n (x,theta) = 0 ∧ (b i).oscillatoryPressure n (x,theta) = 0 ∧
      (g i).oscillation n (x,theta) = 0
  right_zero : ∀ i, i ∉ labels m → ∀ x ∈ U, ∀ theta,
    (b i).oscillation m (e x,theta) = 0 ∧ (b i).oscillatoryPressure m (e x,theta) = 0 ∧
      (g i).oscillation m (e x,theta) = 0

theorem LabelWavesOn.sum {ι : Type} {U : Set Point} {e : Point ≃L[ℝ] Point} {c l : ℝ}
    {labels : ℕ → Finset ι} {b g : ι → HarmonicBlock Point} {n m : ℕ}
    (H : LabelWavesOn U e c l labels b g n m) :
    WaveOn U e c l
      (LabelSumBounds.fieldSum labels (fun i => (b i).oscillation))
      (fun j x => ∑ i ∈ labels j, (b i).oscillatoryPressure j x)
      (LabelSumBounds.fieldSum labels (fun i => (g i).oscillation))
      (LabelSumBounds.fieldSum labels (fun i => (b i).oscillation))
      (fun j x => ∑ i ∈ labels j, (b i).oscillatoryPressure j x)
      (LabelSumBounds.fieldSum labels (fun i => (g i).oscillation)) n m := by
  constructor
  · intro x hx theta j
    apply sum_eq_mul_sum_of_support
    · intro i hi
      exact congrFun (H.left_zero i hi x hx theta).1 j
    · intro i hi
      exact congrFun (H.right_zero i hi x hx theta).1 j
    · intro i
      exact (H.wave i).velocity x hx theta j
  · intro x hx theta
    apply sum_eq_mul_sum_of_support
    · intro i hi
      exact (H.left_zero i hi x hx theta).2.1
    · intro i hi
      exact (H.right_zero i hi x hx theta).2.1
    · intro i
      exact (H.wave i).pressure x hx theta
  · intro x hx theta j
    apply sum_eq_mul_sum_of_support
    · intro i hi
      exact congrFun (H.left_zero i hi x hx theta).2.2 j
    · intro i hi
      exact congrFun (H.right_zero i hi x hx theta).2.2 j
    · intro i
      exact (H.wave i).gaussian x hx theta j

/-! ## Algebraic state operations retain all old errors -/

theorem add_wave_on {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set D} {e : D ≃L[ℝ] E} {c l : ℝ} {u : State D} {ur : State E} {n m : ℕ}
    {w g : Oscillation D} {p : OscillatoryScalar D}
    {wr gr : Oscillation E} {pr : OscillatoryScalar E}
    (H : StateOn U e c l u ur n m) (W : WaveOn U e c l w p g wr pr gr n m) :
    StateOn U e c l
      (u.addIncrement zeroTriple 0 w p ⟨0,g,0⟩)
      (ur.addIncrement zeroTriple 0 wr pr ⟨0,gr,0⟩) n m := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [State.addIncrement, updated_zeroTriple] using H.mean
  · simpa only [State.addIncrement, add_zero] using H.pressure
  · intro x hx theta i
    change u.oscillation n (x,theta) i + w n (x,theta) i = _
    rw [H.oscillation x hx theta i, W.velocity x hx theta i]
    exact (mul_add _ _ _).symm
  · intro x hx theta
    change u.oscillatoryPressure n (x,theta) + p n (x,theta) = _
    rw [H.oscillatoryPressure x hx theta, W.pressure x hx theta]
    exact (mul_add _ _ _).symm
  · simpa only [State.addIncrement, ExcludedErrors.add, add_zero] using H.baseError
  · intro x hx theta i
    change u.errors.gaussian n (x,theta) i + g n (x,theta) i = _
    rw [H.gaussian x hx theta i, W.gaussian x hx theta i]
    exact (mul_add _ _ _).symm
  · simpa only [State.addIncrement, ExcludedErrors.add, add_zero] using H.aliasError

theorem refresh_pressure_alias_on {S T : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
    [NormedAddCommGroup T] [NormedSpace ℝ T]
    {U : Set (PressureStream.Lift S)} {e : PressureStream.Lift S ≃L[ℝ] PressureStream.Lift T}
    {c l : ℝ} {g : VariableGaugeMean.GaugeData S} {gr : VariableGaugeMean.GaugeData T}
    {C : Context (PressureStream.Lift S)} {Cr : Context (PressureStream.Lift T)}
    {old current : State (PressureStream.Lift S)} {oldr currentr : State (PressureStream.Lift T)}
    {n m : ℕ} (H : StateOn U e c l current currentr n m)
    (hnew : ∀ x ∈ U, ∀ theta i,
      VariableGaugeMean.pressureAliasState g C current n (x, theta) i =
        (c * c * l) * VariableGaugeMean.pressureAliasState gr Cr currentr m (e x, theta) i)
    (hold : ∀ x ∈ U, ∀ theta i,
      VariableGaugeMean.pressureAliasState g C old n (x, theta) i =
        (c * c * l) * VariableGaugeMean.pressureAliasState gr Cr oldr m (e x, theta) i) :
    StateOn U e c l (gaugeRefreshPressureAlias g C old current)
      (gaugeRefreshPressureAlias gr Cr oldr currentr) n m := by
  refine ⟨H.mean, H.pressure, H.oscillation, H.oscillatoryPressure, H.baseError, H.gaussian, ?_⟩
  intro x hx theta i
  change current.errors.aliasError n (x,theta) i +
    (VariableGaugeMean.pressureAliasState g C current n (x,theta) i -
      VariableGaugeMean.pressureAliasState g C old n (x,theta) i) =
    (c*c*l) * (currentr.errors.aliasError m (e x,theta) i +
      (VariableGaugeMean.pressureAliasState gr Cr currentr m (e x,theta) i -
        VariableGaugeMean.pressureAliasState gr Cr oldr m (e x,theta) i))
  rw [H.aliasError x hx theta i, hnew x hx theta i, hold x hx theta i]
  ring

/-! ## All analytic source data come from the incoming primitive fields -/

theorem debtRegular_of_primitive {coord a b : ℝ} {U : LocalSignedRequest.SlowRegion coord}
    {c : Context Point} {u : State Point}
    (H : MeanStateRegularity.PrimitiveData U a b c u) (ha : 0 < a) (hab : a < b) (n : ℕ) :
    RankStateCoherence.DebtRegular U.carrier c u n := by
  have hR := H.source ha hab
  have hT := (H.angular_flux ha hab).axial
  have hZ := (H.axial_flux ha hab).axial
  exact ⟨hR.smooth n, hT.smooth n, hZ.smooth n, hR.periodic n, hT.periodic n, hZ.periodic n⟩

namespace Realizes

variable {ι : Type} {G : Geometry} {p : CycleParameters ι} {c : Context Point}

theorem inner_pos (R : Realizes G p c) : 0 < p.gauge.radial.inner := by
  rw [R.gauge]
  exact G.inner_pos

theorem exponent_pos (R : Realizes G p c) : 0 < p.gauge.radial.exponent := by
  rw [R.gauge]
  exact ChartScales.radialExponent_pos G.h G.h_pos.le

theorem length (R : Realizes G p c) (n : ℕ) :
    p.gauge.length n = VariableGaugeMean.qLength (2 * G.h) := by
  rw [R.gauge]
  rfl

theorem gauge_on (R : Realizes G p c) {V : Set Plane} (n m k : ℕ)
    (hi : G.index n + k = G.index m) (htime : ∀ s ∈ V, 0 < s.1) :
    GaugeOn V (bandScale n m) (bandSlowEquiv G.h n m).toContinuousLinearMap k
      p.gauge p.gauge n m := by
  rw [R.gauge]
  exact similarityGaugeOn G.h_pos G.h_lt_half (ChartScales.radialExponent G.h)
    G.inner G.outer G.frequency G.inner_lt_outer G.index n m k hi htime

theorem axial_on (R : Realizes G p c) (n m k : ℕ) :
    ((bandSlowEquiv G.h n m).toContinuousLinearMap.prodMap (TemporalMeanUpdate.coverMap k))
      (c.operators.epsilon n • p.axial) =
        bandScale n m • (c.operators.epsilon m • p.axial) := by
  rw [R.operators, R.axial]
  exact TemporalStateCoherence.band_axial_transport G.h n m k

theorem clock_on (R : Realizes G p c) (n m k : ℕ)
    (hi : G.index n + k = G.index m) :
    TemporalStateCoherence.clock p.timeExponent n (p.commonIndex n) * ChartScales.Tg ^ k =
      (bandVelocityScale G.h n m * bandScale n m) *
        TemporalStateCoherence.clock p.timeExponent m (p.commonIndex m) := by
  rw [R.timeExponent, R.index]
  exact TemporalStateCoherence.clock_band_transport G.h n m (G.index n) (G.index m) k hi

theorem fast_on (R : Realizes G p c) (n m k : ℕ)
    (hi : G.index n + k = G.index m) :
    bandChartEquiv G.h n m k (c.operators.fastCoefficient n • c.operators.vT) =
      (bandVelocityScale G.h n m * bandScale n m) •
        (c.operators.fastCoefficient m • c.operators.vT) := by
  rw [R.operators]
  exact TemporalStateCoherence.common_fast_transport G.h G.index
    G.operatorInner G.operatorOuter G.operator_lt n m k hi

theorem rank_on (R : Realizes G p c) {V : Set Plane} (n m : ℕ)
    (htime : ∀ s ∈ V, 0 < s.1) :
    RankStateCoherence.RankOn V (bandSlowEquiv G.h n m) (bandScale n m)
      (bandVelocityScale G.h n m) p.rank p.rank n m := by
  rw [R.rank]
  exact RankStateCoherence.normalized_rank_on G.h_pos G.h_lt_half
    G.rankAmplitude G.rankShape G.rankInner G.rankOuter n m htime

end Realizes

/-- Intermediate regularity is a proved consequence of the incoming
primitive fields and the two actual covariance changes. -/
structure StagePrimitives {ι : Type} (G : Geometry) (p : CycleParameters ι)
    (v : CycleCoefficients ι) (c : Context Point) (u : State Point)
    (U : LocalSignedRequest.SlowRegion (2 * G.h)) : Prop where
  particular : MeanStateRegularity.PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c
    (p.afterParticular v c u)
  signed : MeanStateRegularity.PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c
    (p.afterSigned v c u)
  temporal : MeanStateRegularity.PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c
    (p.afterTemporal v c u)
  ranked : MeanStateRegularity.PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c
    (p.afterRank v c u)
  rankGeometry : LocalRankDefect.RankGeometry p.gauge p.rank U.carrier c (p.afterTemporal v c u)

theorem stage_primitives {ι : Type} {G : Geometry} {p : CycleParameters ι}
    {v : CycleCoefficients ι} {c : Context Point} {u : State Point}
    {U : LocalSignedRequest.SlowRegion (2 * G.h)} (R : Realizes G p c)
    (H : MeanStateRegularity.PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c u)
    (hX₁ : ∀ i j, GaugeMomentBalances.MovingField U p.gauge.radial.inner p.gauge.radial.outer
      (SignedMeanGain.covarianceIncrement u.oscillation (p.particularVelocity v c u) i j))
    (hX₂ : ∀ i j, GaugeMomentBalances.MovingField U p.gauge.radial.inner p.gauge.radial.outer
      (SignedMeanGain.covarianceIncrement (p.afterParticular v c u).oscillation (p.signedVelocity v
          c u) i j))
    (hg : LocalRankDefect.RankGeometry p.gauge p.rank U.carrier c u) :
    StagePrimitives G p v c u U := by
  have H₁ := H.waveStage p.gauge (p.particularVelocity v c u) (p.particularPressure v c u)
    (p.particularGaussian v c u) hX₁
  have H₂ := H₁.waveStage p.gauge (p.signedVelocity v c u) (p.signedPressure v c u)
    (p.signedGaussian v c u) hX₂
  have H₃ := MeanStageRegularity.temporalStage_primitive H₂ R.inner_pos R.exponent_pos R.length rfl
    p.timeExponent p.commonIndex p.axial
  have Hgeom := MeanStageRegularity.rankGeometry_for_state H₃ R.inner_pos
      p.gauge.radial.inner_lt_outer hg
  have H₄ := MeanStageRegularity.rankStage_primitive H₃ Hgeom R.length p.axial
  exact ⟨H₁, H₂, H₃, H₄, Hgeom⟩

section OnePair

variable {ι : Type} {G : Geometry} {p : CycleParameters ι} {v : CycleCoefficients ι}
  {c : Context Point} {u : State Point} (R : Realizes G p c)
  {U : LocalSignedRequest.SlowRegion (2 * G.h)} {V : Set Plane}
  (hV : IsOpen V) (hsub : V ⊆ U.carrier) (n m k : ℕ)
  (hi : G.index n + k = G.index m) (hmap : MapsTo (bandSlowEquiv G.h n m) V U.carrier)
  (HC : ContextBand G V n m k c)

include R hV hsub hi hmap HC

theorem reconstruction_and_alias_band
    (H : MeanStateRegularity.PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c u)
    (HS : StateBand G V n m k u) :
    StateBand G V n m k (VariableGaugeMean.reconstructState p.gauge c u) ∧
      ∀ x ∈ PhysicalMeanDomain.slowDomain V, ∀ theta i,
        VariableGaugeMean.pressureAliasState p.gauge c u n (x,theta) i =
          (bandVelocityScale G.h n m * bandVelocityScale G.h n m * bandScale n m) *
            VariableGaugeMean.pressureAliasState p.gauge c u m (bandChartEquiv G.h n m k x,theta) i
                := by
  have hg := R.gauge_on n m k hi (fun s hs => U.time_pos s (hsub hs))
  have hr := H.source R.inner_pos p.gauge.radial.inner_lt_outer
  have hs : VariableGaugeMean.SupportedGauge p.gauge.radial.inner p.gauge.radial.outer
      (p.gauge.length m) U.carrier (u.gr c m) := by
    rw [R.length]
    exact hr.supported m
  exact ⟨GaugeStateCoherence.reconstructState_on (bandScale_pos n m) (bandSlowEquiv G.h n m) k
    hV U.isOpen hmap p.gauge p.gauge c c u u n m R.inner_pos R.exponent_pos hg HS HC
    (hr.smooth m) (hr.periodic m) hs,
    GaugeStateCoherence.pressureAliasState_on (bandScale_pos n m) (bandSlowEquiv G.h n m) k
    hV U.isOpen hmap p.gauge p.gauge c c u u n m R.inner_pos R.exponent_pos hg HS HC
    (hr.smooth m) (hr.periodic m) hs⟩

theorem wave_stage_band {w g : Oscillation Point} {q : OscillatoryScalar Point}
    (H : MeanStateRegularity.PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c u)
    (HS : StateBand G V n m k u)
    (hX : ∀ i j, GaugeMomentBalances.MovingField U p.gauge.radial.inner p.gauge.radial.outer
      (SignedMeanGain.covarianceIncrement u.oscillation w i j))
    (HW : WaveOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv G.h n m k)
      (bandVelocityScale G.h n m) (bandScale n m) w q g w q g n m) :
    StateBand G V n m k (gaugeWaveStage p.gauge c u w q ⟨0,g,0⟩) := by
  have HP := H.waveStage p.gauge w q g hX
  have Hbefore : MeanStateRegularity.PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c
      (u.addIncrement zeroTriple 0 w q ⟨0,g,0⟩) :=
    ⟨HP.operators, HP.base, HP.mean, HP.covariance, HP.virtualTheta, HP.virtualAxial⟩
  exact (reconstruction_and_alias_band R hV hsub n m k hi hmap HC Hbefore (add_wave_on HS HW)).1

end OnePair

/-- Error band as an element of `Prop`. -/
def ErrorBand (G : Geometry) (V : Set Plane) (n m k : ℕ) (a : Oscillation Point) : Prop :=
  ∀ x ∈ PhysicalMeanDomain.slowDomain V, ∀ theta i,
    a n (x,theta) i = (bandVelocityScale G.h n m * bandVelocityScale G.h n m * bandScale n m) *
      a m (bandChartEquiv G.h n m k x,theta) i

/-- Only the two actual per-label wave insertions occur in this input.
The state, reconstructed pressures and mean increments are not inputs. -/
structure CycleWavesOn {ι : Type} (G : Geometry) (p : CycleParameters ι)
    (v : CycleCoefficients ι) (c : Context Point) (u : State Point)
    (V : Set Plane) (n m k : ℕ) : Prop where
  particular : LabelWavesOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv G.h n m k)
    (bandVelocityScale G.h n m) (bandScale n m) v.labels
    (p.particularBlock v c u) (p.particularGaussianBlock v c u) n m
  signed : LabelWavesOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv G.h n m k)
    (bandVelocityScale G.h n m) (bandScale n m) v.labels
    (p.signedBlock v c u) (p.signedGaussianBlock v c u) n m

/-- A derived transport certificate for all four literal stages and the
three aliases needed by the final pressure-alias replacement. -/
structure CycleTransport {ι : Type} (G : Geometry) (p : CycleParameters ι)
    (v : CycleCoefficients ι) (c : Context Point) (u : State Point)
    (V : Set Plane) (n m k : ℕ) : Prop where
  particular : StateBand G V n m k (p.afterParticular v c u)
  signed : StateBand G V n m k (p.afterSigned v c u)
  temporal : StateBand G V n m k (p.afterTemporal v c u)
  ranked : StateBand G V n m k (p.afterRank v c u)
  next : StateBand G V n m k (p.next v c u)
  temporalAlias : ErrorBand G V n m k
    (VariableGaugeMean.temporalAliasState p.gauge p.timeExponent p.commonIndex c (p.afterSigned v c
        u))
  oldPressureAlias : ErrorBand G V n m k (VariableGaugeMean.pressureAliasState p.gauge c u)
  currentPressureAlias : ErrorBand G V n m k
    (VariableGaugeMean.pressureAliasState p.gauge c (p.afterRank v c u))

theorem cycle_transport {ι : Type} {G : Geometry} {p : CycleParameters ι}
    {v : CycleCoefficients ι} {c : Context Point} {u : State Point}
    {U : LocalSignedRequest.SlowRegion (2 * G.h)} {V : Set Plane}
    (R : Realizes G p c) (hV : IsOpen V) (hsub : V ⊆ U.carrier) (n m k : ℕ)
    (hi : G.index n + k = G.index m) (hmap : MapsTo (bandSlowEquiv G.h n m) V U.carrier)
    (HC : ContextBand G V n m k c) (HS : StateBand G V n m k u)
    (H : MeanStateRegularity.PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c u)
    (hX₁ : ∀ i j, GaugeMomentBalances.MovingField U p.gauge.radial.inner p.gauge.radial.outer
      (SignedMeanGain.covarianceIncrement u.oscillation (p.particularVelocity v c u) i j))
    (hX₂ : ∀ i j, GaugeMomentBalances.MovingField U p.gauge.radial.inner p.gauge.radial.outer
      (SignedMeanGain.covarianceIncrement (p.afterParticular v c u).oscillation (p.signedVelocity v
          c u) i j))
    (hg : LocalRankDefect.RankGeometry p.gauge p.rank U.carrier c u)
    (HW : CycleWavesOn G p v c u V n m k) : CycleTransport G p v c u V n m k := by
  have HP := stage_primitives R H hX₁ hX₂ hg
  have H₁ : StateBand G V n m k (p.afterParticular v c u) :=
    wave_stage_band R hV hsub n m k hi hmap HC H HS hX₁ HW.particular.sum
  have H₂ : StateBand G V n m k (p.afterSigned v c u) :=
    wave_stage_band R hV hsub n m k hi hmap HC HP.particular H₁ hX₂ HW.signed.sum
  have htime : ∀ s ∈ V, 0 < s.1 := fun s hs => U.time_pos s (hsub hs)
  have hGauge := R.gauge_on n m k hi htime
  have hTheta := HP.signed.theta R.inner_pos p.gauge.radial.inner_lt_outer
  have hAxial := HP.signed.axial_reconstructed R.inner_pos R.exponent_pos R.length rfl
  have hTemporalSource := HP.temporal.source R.inner_pos p.gauge.radial.inner_lt_outer
  have hAxialSupport : VariableGaugeMean.SupportedGauge p.gauge.radial.inner p.gauge.radial.outer
      (p.gauge.length m) U.carrier ((p.afterSigned v c u).axialResidual c m) := by
    rw [R.length]
    exact hAxial.supported m
  have hTemporalSupport : VariableGaugeMean.SupportedGauge p.gauge.radial.inner p.gauge.radial.outer
      (p.gauge.length m) U.carrier ((p.afterTemporal v c u).gr c m) := by
    rw [R.length]
    exact hTemporalSource.supported m
  have H₃ : StateBand G V n m k (p.afterTemporal v c u) :=
    TemporalStateCoherence.temporalStage_on (bandScale_pos n m) (bandSlowEquiv G.h n m) k
      hV U.isOpen hmap p.gauge p.gauge c c (p.afterSigned v c u) (p.afterSigned v c u)
      p.timeExponent p.commonIndex p.commonIndex n m R.inner_pos R.exponent_pos hGauge H₂ HC
      (R.clock_on n m k hi) (hAxial.smooth m) (hAxial.periodic m) hAxialSupport
      p.axial p.axial (R.axial_on n m k) (hTheta.smooth m) (hTheta.periodic m) (R.fast_on n m k hi)
      (hTemporalSource.smooth m) (hTemporalSource.periodic m) hTemporalSupport
  have hAlias : ErrorBand G V n m k
      (VariableGaugeMean.temporalAliasState p.gauge p.timeExponent p.commonIndex c (p.afterSigned v
          c u)) :=
    TemporalStateCoherence.temporalAliasState_on (bandScale_pos n m) (bandSlowEquiv G.h n m) k
      hV U.isOpen hmap p.gauge p.gauge c c (p.afterSigned v c u) (p.afterSigned v c u)
      p.timeExponent p.commonIndex p.commonIndex n m R.inner_pos R.exponent_pos hGauge H₂ HC
      (R.clock_on n m k hi) (hAxial.smooth m) (hAxial.periodic m) hAxialSupport
      p.axial p.axial (R.axial_on n m k) (hTheta.smooth m) (hTheta.periodic m) (R.fast_on n m k hi)
  have hRankSource := HP.ranked.source R.inner_pos p.gauge.radial.inner_lt_outer
  have hRankSupport : VariableGaugeMean.SupportedGauge p.gauge.radial.inner p.gauge.radial.outer
      (p.gauge.length m) U.carrier ((p.afterRank v c u).gr c m) := by
    rw [R.length]
    exact hRankSource.supported m
  have H₄ : StateBand G V n m k (p.afterRank v c u) :=
    RankStateCoherence.rankStageState_on (bandScale_pos n m)
      (Real.rpow_pos_of_pos (div_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m)) _).ne'
      (bandSlowEquiv G.h n m) k hV U.isOpen hmap H₃ HC
      (debtRegular_of_primitive HP.temporal R.inner_pos p.gauge.radial.inner_lt_outer m)
      (R.rank_on n m htime) hGauge HP.rankGeometry p.axial p.axial (R.axial_on n m k)
      (hRankSource.smooth m) (hRankSource.periodic m) hRankSupport
  have hOld := (reconstruction_and_alias_band R hV hsub n m k hi hmap HC H HS).2
  have hNew := (reconstruction_and_alias_band R hV hsub n m k hi hmap HC HP.ranked H₄).2
  exact ⟨H₁, H₂, H₃, H₄, refresh_pressure_alias_on H₄ hNew hOld, hAlias, hOld, hNew⟩

theorem CycleTransport.axis {ι : Type} {G : Geometry} {p : CycleParameters ι}
    {v : CycleCoefficients ι} {c : Context Point} {u : State Point}
    {V : Set Plane} {n m k : ℕ} (H : CycleTransport G p v c u V n m k)
    {a : AxisymmetricAlias} (HA : AxisBand G V n m k a) :
    AxisBand G V n m k (p.nextAxisymmetricAlias v c u a) := by
  intro x hx i
  change a n x i +
    VariableGaugeMean.temporalAliasState p.gauge p.timeExponent p.commonIndex c (p.afterSigned v c
        u) n (x,0) i +
    (VariableGaugeMean.pressureAliasState p.gauge c (p.afterRank v c u) n (x,0) i -
      VariableGaugeMean.pressureAliasState p.gauge c u n (x,0) i) = _
  rw [HA x hx i, H.temporalAlias x hx 0 i, H.currentPressureAlias x hx 0 i, H.oldPressureAlias x hx
      0 i]
  change _ = (bandVelocityScale G.h n m * bandVelocityScale G.h n m * bandScale n m) *
    (a m (bandChartEquiv G.h n m k x) i +
      VariableGaugeMean.temporalAliasState p.gauge p.timeExponent p.commonIndex c (p.afterSigned v
          c u) m
        (bandChartEquiv G.h n m k x,0) i +
      (VariableGaugeMean.pressureAliasState p.gauge c (p.afterRank v c u) m (bandChartEquiv G.h n m
          k x,0) i -
        VariableGaugeMean.pressureAliasState p.gauge c u m (bandChartEquiv G.h n m k x,0) i))
  ring

theorem CycleTransport.step {ι : Type} {G : Geometry} {p : CycleParameters ι}
    {x : CycleState ι} {c : Context Point} {V : Set Plane} {n m k : ℕ}
    (H : CycleTransport G p x.coefficients c x.state V n m k)
    (HA : AxisBand G V n m k x.axisymmetricAlias) :
    StateBand G V n m k (x.step p c).state ∧
      AxisBand G V n m k (x.step p c).axisymmetricAlias := ⟨H.next, H.axis HA⟩

/-- Stored labels and harmonic aliases are never reselected by a cycle. -/
theorem step_labels {ι : Type} (p : CycleParameters ι) (c : Context Point) (x : CycleState ι) :
    (x.step p c).coefficients.labels = x.coefficients.labels := rfl

theorem step_aliasCoefficients {ι : Type} (p : CycleParameters ι) (c : Context Point)
    (x : CycleState ι) :
    (x.step p c).coefficients.aliasCoefficients = x.coefficients.aliasCoefficients := rfl

theorem iterate_labels {ι : Type} (p : ℕ → CycleParameters ι) (c : Context Point)
    (seed : CycleState ι) (j : ℕ) :
    (CycleState.iterate p c seed j).coefficients.labels = seed.coefficients.labels := by
  induction j with
  | zero => rfl
  | succ j ih => exact ih

theorem iterate_aliasCoefficients {ι : Type} (p : ℕ → CycleParameters ι) (c : Context Point)
    (seed : CycleState ι) (j : ℕ) :
    (CycleState.iterate p c seed j).coefficients.aliasCoefficients =
        seed.coefficients.aliasCoefficients := by
  induction j with
  | zero => rfl
  | succ j ih => exact ih

/-- The primitive wave laws also propagate the complete individual
harmonic blocks, so they remain available to the next reference solve. -/
theorem block_fields_next {ι : Type} {G : Geometry} {p : CycleParameters ι}
    {v : CycleCoefficients ι} {c : Context Point} {u : State Point}
    {V : Set Plane} {n m k : ℕ} (HW : CycleWavesOn G p v c u V n m k)
    (hc : ∀ l, SameCarrier (v.blocks l) (p.signedBlock v c u l)) (l : ι)
    (H : BlockFieldsOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv G.h n m k)
      (bandVelocityScale G.h n m) (bandScale n m) (v.blocks l) (v.blocks l)
      (v.gaussian l) (v.aliasCoefficients l) (v.gaussian l) (v.aliasCoefficients l) n m) :
    BlockFieldsOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv G.h n m k)
      (bandVelocityScale G.h n m) (bandScale n m)
      ((p.nextCoefficients v c u).blocks l) ((p.nextCoefficients v c u).blocks l)
      ((p.nextCoefficients v c u).gaussian l) ((p.nextCoefficients v c u).aliasCoefficients l)
      ((p.nextCoefficients v c u).gaussian l) ((p.nextCoefficients v c u).aliasCoefficients l) n m
          := by
  refine ⟨H.phase, H.angular, H.angular_ne, ?_, ?_, ?_, H.aliasError⟩
  · intro x hx theta i
    change (p.finalBlock v c u l).oscillation n (x,theta) i =
      bandVelocityScale G.h n m * (p.finalBlock v c u l).oscillation m (bandChartEquiv G.h n m k
          x,theta) i
    rw [p.finalBlock_oscillation v c u hc l]
    simp only [Pi.add_apply]
    rw [H.velocity x hx theta i, (HW.particular.wave l).velocity x hx theta i,
      (HW.signed.wave l).velocity x hx theta i]
    ring
  · intro x hx theta
    change (p.finalBlock v c u l).oscillatoryPressure n (x,theta) =
      (bandVelocityScale G.h n m * bandVelocityScale G.h n m) *
        (p.finalBlock v c u l).oscillatoryPressure m (bandChartEquiv G.h n m k x,theta)
    rw [p.finalBlock_pressure v c u hc l]
    simp only [Pi.add_apply]
    rw [H.pressure x hx theta, (HW.particular.wave l).pressure x hx theta,
      (HW.signed.wave l).pressure x hx theta]
    ring
  · intro x hx theta i
    change coefficientField ((p.nextCoefficients v c u).blocks l) ((p.nextCoefficients v c
        u).gaussian l) n (x,theta) i =
      (bandVelocityScale G.h n m * bandVelocityScale G.h n m * bandScale n m) *
        coefficientField ((p.nextCoefficients v c u).blocks l) ((p.nextCoefficients v c u).gaussian
            l) m
          (bandChartEquiv G.h n m k x,theta) i
    rw [p.nextCoefficients_gaussian_field v c u hc l n (x,theta) i,
      p.nextCoefficients_gaussian_field v c u hc l m (bandChartEquiv G.h n m k x,theta) i]
    have he := H.gaussian x hx theta i
    change coefficientField (v.blocks l) (v.gaussian l) n (x,theta) i = _ at he
    rw [he, (HW.particular.wave l).gaussian x hx theta i, (HW.signed.wave l).gaussian x hx theta i]
    simp only [coefficientField]
    ring

/-- One fixed geometry and one fixed slow domain suffice for the entire
actual recurrence. Only each stage's two native wave laws and covariance
changes are supplied; next-state coherence is proved by induction. -/
theorem iterate_state_axis {ι : Type} (G : Geometry) (p : ℕ → CycleParameters ι)
    (c : Context Point) (seed : CycleState ι)
    (R : ∀ j, Realizes G (p j) c)
    {U : LocalSignedRequest.SlowRegion (2 * G.h)} {V : Set Plane}
    (hV : IsOpen V) (hsub : V ⊆ U.carrier) (n m k : ℕ)
    (hi : G.index n + k = G.index m) (hmap : MapsTo (bandSlowEquiv G.h n m) V U.carrier)
    (HC : ContextBand G V n m k c)
    (HS : StateBand G V n m k seed.state) (HA : AxisBand G V n m k seed.axisymmetricAlias)
    (HP : MeanStateRegularity.PrimitiveData U G.inner G.outer c seed.state)
    (HG : LocalRankDefect.RankGeometry G.gauge G.rank U.carrier c seed.state)
    (hX₁ : ∀ j, let x := CycleState.iterate p c seed j
      ∀ i l, GaugeMomentBalances.MovingField U G.inner G.outer
        (SignedMeanGain.covarianceIncrement x.state.oscillation
          ((p j).particularVelocity x.coefficients c x.state) i l))
    (hX₂ : ∀ j, let x := CycleState.iterate p c seed j
      ∀ i l, GaugeMomentBalances.MovingField U G.inner G.outer
        (SignedMeanGain.covarianceIncrement ((p j).afterParticular x.coefficients c
            x.state).oscillation
          ((p j).signedVelocity x.coefficients c x.state) i l))
    (HW : ∀ j, let x := CycleState.iterate p c seed j
      CycleWavesOn G (p j) x.coefficients c x.state V n m k) :
    ∀ j, StateBand G V n m k (CycleState.iterate p c seed j).state ∧
      AxisBand G V n m k (CycleState.iterate p c seed j).axisymmetricAlias ∧
      MeanStateRegularity.PrimitiveData U G.inner G.outer c (CycleState.iterate p c seed j).state
          := by
  intro j
  induction j with
  | zero => exact ⟨HS, HA, HP⟩
  | succ j ih =>
    let x := CycleState.iterate p c seed j
    have hinner : (p j).gauge.radial.inner = G.inner := by rw [(R j).gauge]; rfl
    have houter : (p j).gauge.radial.outer = G.outer := by rw [(R j).gauge]; rfl
    have Hp : MeanStateRegularity.PrimitiveData U (p j).gauge.radial.inner (p j).gauge.radial.outer
        c x.state := by
      rw [hinner, houter]
      exact ih.2.2
    have Hrank : LocalRankDefect.RankGeometry (p j).gauge (p j).rank U.carrier c x.state := by
      rw [(R j).gauge, (R j).rank]
      exact MeanStageRegularity.rankGeometry_for_state ih.2.2 G.inner_pos G.inner_lt_outer HG
    have HX₁ : ∀ i l, GaugeMomentBalances.MovingField U (p j).gauge.radial.inner (p
        j).gauge.radial.outer
        (SignedMeanGain.covarianceIncrement x.state.oscillation ((p j).particularVelocity
            x.coefficients c x.state) i l) := by
      rw [hinner, houter]
      exact hX₁ j
    have HX₂ : ∀ i l, GaugeMomentBalances.MovingField U (p j).gauge.radial.inner (p
        j).gauge.radial.outer
        (SignedMeanGain.covarianceIncrement ((p j).afterParticular x.coefficients c
            x.state).oscillation
          ((p j).signedVelocity x.coefficients c x.state) i l) := by
      rw [hinner, houter]
      exact hX₂ j
    have Hnext := cycle_transport (R j) hV hsub n m k hi hmap HC ih.1 Hp HX₁ HX₂ Hrank (HW j)
    have Hprimitive := ((p j).next_primitive x.coefficients c x.state U
      (R j).inner_pos (R j).exponent_pos (R j).length Hp HX₁ HX₂ Hrank).1
    rw [hinner, houter] at Hprimitive
    exact ⟨Hnext.next, Hnext.axis ih.2.1, Hprimitive⟩

theorem iterate_block_fields {ι : Type} (G : Geometry) (p : ℕ → CycleParameters ι)
    (c : Context Point) (seed : CycleState ι) (V : Set Plane) (n m k : ℕ)
    (Hseed : ∀ l, BlockFieldsOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv G.h n m k)
      (bandVelocityScale G.h n m) (bandScale n m) (seed.coefficients.blocks l)
          (seed.coefficients.blocks l)
      (seed.coefficients.gaussian l) (seed.coefficients.aliasCoefficients l)
      (seed.coefficients.gaussian l) (seed.coefficients.aliasCoefficients l) n m)
    (HW : ∀ j, let x := CycleState.iterate p c seed j
      CycleWavesOn G (p j) x.coefficients c x.state V n m k)
    (hc : ∀ j l, let x := CycleState.iterate p c seed j
      SameCarrier (x.coefficients.blocks l) ((p j).signedBlock x.coefficients c x.state l)) :
    ∀ j l, let x := CycleState.iterate p c seed j
      BlockFieldsOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv G.h n m k)
        (bandVelocityScale G.h n m) (bandScale n m) (x.coefficients.blocks l)
            (x.coefficients.blocks l)
        (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l)
        (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l) n m := by
  intro j
  induction j with
  | zero => exact Hseed
  | succ j ih => exact fun l => block_fields_next (HW j) (hc j) l (ih l)

/-! ## Explicit retention of the current pressure and all temporal aliases -/

/-- Temporal alias at as an element of `Oscillation Point`. -/
noncomputable def temporalAliasAt {ι : Type} (p : ℕ → CycleParameters ι)
    (c : Context Point) (seed : CycleState ι) (j : ℕ) : Oscillation Point :=
  let x := CycleState.iterate p c seed j
  VariableGaugeMean.temporalAliasState (p j).gauge (p j).timeExponent (p j).commonIndex c
    ((p j).afterSigned x.coefficients c x.state)

/-- The obsolete pressure alias cancels at every step. The initial alias,
every earlier temporal alias, and exactly one current pressure alias are
retained with their actual signs. This is an identity of full fields. -/
theorem iterate_alias_error {ι : Type} (p : ℕ → CycleParameters ι) (c : Context Point)
    (seed : CycleState ι) (g : VariableGaugeMean.GaugeData Plane)
    (hg : ∀ j, (p j).gauge = g) (J : ℕ) :
    (CycleState.iterate p c seed J).state.errors.aliasError =
      seed.state.errors.aliasError + (∑ j ∈ Finset.range J, temporalAliasAt p c seed j) +
        (VariableGaugeMean.pressureAliasState g c (CycleState.iterate p c seed J).state -
          VariableGaugeMean.pressureAliasState g c seed.state) := by
  induction J with
  | zero => simp only [CycleState.iterate_zero, Finset.sum_range_zero, add_zero, sub_self]
  | succ J ih =>
    let x := CycleState.iterate p c seed J
    have hstep : (x.step (p J) c).state.errors.aliasError =
        x.state.errors.aliasError + temporalAliasAt p c seed J +
          (VariableGaugeMean.pressureAliasState g c (x.step (p J) c).state -
            VariableGaugeMean.pressureAliasState g c x.state) := by
      rw [show (x.step (p J) c).state = (p J).next x.coefficients c x.state from rfl,
        (p J).next_alias_error x.coefficients c x.state]
      simp only [temporalAliasAt, hg J]
      rfl
    rw [CycleState.iterate_succ, hstep, Finset.sum_range_succ]
    change x.state.errors.aliasError + _ + _ = _
    rw [show x.state.errors.aliasError = _ from ih]
    abel

theorem iterate_alias_separated {ι : Type} (p : ℕ → CycleParameters ι) (c : Context Point)
    (seed : CycleState ι) (g : VariableGaugeMean.GaugeData Plane)
    (hg : ∀ j, (p j).gauge = g) (other : Oscillation Point)
    (hseed : seed.state.errors.aliasError = other + VariableGaugeMean.pressureAliasState g c
        seed.state)
    (J : ℕ) :
    (CycleState.iterate p c seed J).state.errors.aliasError =
      other + (∑ j ∈ Finset.range J, temporalAliasAt p c seed j) +
        VariableGaugeMean.pressureAliasState g c (CycleState.iterate p c seed J).state := by
  rw [iterate_alias_error p c seed g hg J, hseed]
  abel

/-- Reference transport on positive radii extends to the entire required
fiber when the actual supported wave fields vanish at nonpositive radii.
No assertion is inferred from physical-graph equality. -/
theorem waveOn_of_positive_fibers (h : ℝ) (n m k : ℕ) {V U : Set Plane}
    (hmap : MapsTo (bandSlowEquiv h n m) V U)
    (w g : Oscillation Point) (q : OscillatoryScalar Point)
    (H : WaveOn (PhysicalMeanDomain.slowDomain V ∩ {x | 0 < x.1}) (bandChartEquiv h n m k)
      (bandVelocityScale h n m) (bandScale n m) w q g w q g n m)
    (hzleft : ∀ x ∈ PhysicalMeanDomain.slowDomain V, x.1 ≤ 0 → ∀ theta,
      w n (x, theta) = 0 ∧ q n (x, theta) = 0 ∧ g n (x, theta) = 0)
    (hzright : ∀ x ∈ PhysicalMeanDomain.slowDomain U, x.1 ≤ 0 → ∀ theta,
      w m (x, theta) = 0 ∧ q m (x, theta) = 0 ∧ g m (x, theta) = 0) :
    WaveOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv h n m k)
      (bandVelocityScale h n m) (bandScale n m) w q g w q g n m := by
  have he (x : Point) (hx : x ∈ PhysicalMeanDomain.slowDomain V) (theta : ℝ) :
      (∀ i, w n (x,theta) i = bandVelocityScale h n m * w m (bandChartEquiv h n m k x,theta) i) ∧
      (q n (x,theta) = (bandVelocityScale h n m * bandVelocityScale h n m) *
        q m (bandChartEquiv h n m k x,theta)) ∧
      (∀ i, g n (x,theta) i = (bandVelocityScale h n m * bandVelocityScale h n m * bandScale n m) *
        g m (bandChartEquiv h n m k x,theta) i) := by
    by_cases hr : 0 < x.1
    · exact ⟨H.velocity x ⟨hx,hr⟩ theta, H.pressure x ⟨hx,hr⟩ theta, H.gaussian x ⟨hx,hr⟩ theta⟩
    · have hx' : bandChartEquiv h n m k x ∈ PhysicalMeanDomain.slowDomain U := hmap hx
      have hr' : (bandChartEquiv h n m k x).1 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (bandScale_pos n m).le (le_of_not_gt hr)
      have hleft := hzleft x hx (le_of_not_gt hr) theta
      have hright := hzright _ hx' hr' theta
      simp only [hleft.1, hright.1, hleft.2.1, hright.2.1, hleft.2.2, hright.2.2,
        Pi.zero_apply, mul_zero, implies_true, and_self]
  exact ⟨fun x hx theta => (he x hx theta).1, fun x hx theta => (he x hx theta).2.1,
    fun x hx theta => (he x hx theta).2.2⟩

end NavierStokes.CycleStateCoherence

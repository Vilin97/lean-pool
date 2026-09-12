/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualMeanPotentialRealization
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualInitialization
import LeanPool.NavierStokesAndEuler.NavierStokes.MeanStageRegularity
public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectionStep
public import LeanPool.NavierStokesAndEuler.NavierStokes.TemporalStateCoherence
public import LeanPool.NavierStokesAndEuler.NavierStokes.RankStateCoherence

/-!
# Physical mean fields glued from their actual valid bands

Only overlapping valid slow strips are compared. The physical field is
defined by a valid-band choice, and its value is proved independent of that
choice. Native moving mean classes supply the physical derivative estimates.
-/

section

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

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.ActualMeanPhysicalData

open Set Function Filter ProblemStatement
open PhysicalResidualNaturality GaugeStateCoherence
open scoped Topology ContDiff BigOperators

/-- Plane: an abbreviation for `PressureStream.Plane`. -/
abbrev Plane := PressureStream.Plane
/-- Point: an abbreviation for `PressureStream.Lift Plane`. -/
abbrev Point := PressureStream.Lift Plane
/-- Scalar: an abbreviation for `ℕ → Point → ℝ`. -/
abbrev Scalar := ℕ → Point → ℝ

/-- One common index and one band floor for every field in the construction. -/
structure Atlas (h : ℝ) (N Δ : ℕ) where
  /-- Index of `Atlas`, of type `ℕ → ℕ`. -/
  index : ℕ → ℕ
  index_le : ∀ n ≥ N, index n ≤ ChartScales.nativeIndex h n
  gap_le : ∀ n ≥ N, ChartScales.nativeIndex h n - index n ≤ Δ

/-- Gap, given by `ChartScales.nativeIndex h n - A.index n`. -/
noncomputable def Atlas.gap {h : ℝ} {N Δ : ℕ} (A : Atlas h N Δ) (n : ℕ) : ℕ :=
  ChartScales.nativeIndex h n - A.index n

theorem Atlas.index_eq {h : ℝ} {N Δ : ℕ} (A : Atlas h N Δ) {n : ℕ} (hn : N ≤ n) :
    ChartScales.nativeIndex h n - A.gap n = A.index n :=
  Nat.sub_sub_self (A.index_le n hn)

/-- Common atlas, bundling `index`, `index_le`, `gap_le`. -/
noncomputable def commonAtlas (h : ℝ) (hh : 0 ≤ h) (N : ℕ) :
    Atlas h N (CorrectionInitialization.CommonWindow.gap h) where
  index := CorrectionInitialization.CommonWindow.index h
  index_le n _ := CorrectionInitialization.CommonWindow.index_le_native h n
  gap_le n _ := CorrectionInitialization.CommonWindow.gap_le h hh n

/-- Chart, given by `VariableGaugeMean.physicalToChartTZ h n (A.index n)`. -/
noncomputable def Atlas.chart {h : ℝ} {N Δ : ℕ} (A : Atlas h N Δ) (n : ℕ) : Point →L[ℝ] Point :=
  VariableGaugeMean.physicalToChartTZ h n (A.index n)

/-- Overlap, given by `U ∩ (bandSlowEquiv h n m) ⁻¹' U`. -/
noncomputable def overlap (h : ℝ) (U : Set Plane) (n m : ℕ) : Set Plane :=
  U ∩ (bandSlowEquiv h n m) ⁻¹' U

theorem overlap_open (h : ℝ) {U : Set Plane} (hU : IsOpen U) (n m : ℕ) :
    IsOpen (overlap h U n m) :=
  hU.inter (hU.preimage (bandSlowEquiv h n m).continuous)

theorem power_scale_cancel (hdegree : ℝ) (n m : ℕ) :
    ChartScales.Q n ^ (-hdegree) * (ChartScales.Q n / ChartScales.Q m) ^ hdegree =
      ChartScales.Q m ^ (-hdegree) := by
  rw [Real.div_rpow (ChartScales.Q_pos n).le (ChartScales.Q_pos m).le,
    ← mul_div_assoc, ← Real.rpow_add (ChartScales.Q_pos n), neg_add_cancel,
    Real.rpow_zero, one_div, Real.rpow_neg (ChartScales.Q_pos m).le]

theorem coverMap_comp (i k : ℕ) (Y : Plane) :
    TemporalMeanUpdate.coverMap k (TemporalMeanUpdate.coverMap i Y) =
      TemporalMeanUpdate.coverMap (i + k) Y := by
  simp only [MeanChartCompatibility.coverMap_eq_coverPower, CommonCoverSolve.coverPower_apply]
  rw [add_comm i k, pow_add, _root_.mul_apply_eq_comp]

theorem bandChart_chart {h : ℝ} {N Δ : ℕ} (A : Atlas h N Δ)
    (n m k : ℕ) (hi : A.index n + k = A.index m) (z : Point) :
    bandChartEquiv h n m k (A.chart n z) = A.chart m z := by
  simp only [Atlas.chart, bandChartEquiv_apply, PhysicalMeanJetBounds.physicalToChartTZ_apply,
    bandSlowEquiv_apply, coverMap_comp, hi]
  apply Prod.ext
  · change (ChartScales.Q n / ChartScales.Q m) ^ (1 / 2 : ℝ) *
      (ChartScales.Q n ^ (-(1 / 2 : ℝ)) * z.1) = _
    rw [mul_left_comm, ← mul_assoc, power_scale_cancel]
    rfl
  · apply Prod.ext
    · apply Prod.ext
      · simp only [Real.rpow_neg_one]
        field_simp [(ChartScales.Q_pos n).ne', (ChartScales.Q_pos m).ne']
      · change (ChartScales.Q n / ChartScales.Q m) ^ CoordinateAlgebra.D h *
          (ChartScales.Q n ^ (-CoordinateAlgebra.D h) * z.2.1.2) = _
        rw [mul_left_comm, ← mul_assoc, power_scale_cancel]
    · rfl

/-- This law is required only where both original band formulas are valid. -/
def Atlas.OverlapLaw {h : ℝ} {N Δ : ℕ} (A : Atlas h N Δ)
    (U : Set Plane) (degree : ℝ) (f : Scalar) : Prop :=
  ∀ n ≥ N, ∀ m ≥ N, ∀ k, A.index n + k = A.index m →
    ∀ x : Point, x.2.1 ∈ overlap h U n m →
      f n x = (ChartScales.Q n / ChartScales.Q m) ^ degree * f m (bandChartEquiv h n m k x)

/-- Valid, given by `N ≤ n ∧ 0 < z.2.1.1 ∧ (A.chart n z).2.1 ∈ U`. -/
def Atlas.Valid {h : ℝ} {N Δ : ℕ} (A : Atlas h N Δ)
    (U : Set Plane) (z : Point) (n : ℕ) : Prop :=
  N ≤ n ∧ 0 < z.2.1.1 ∧ (A.chart n z).2.1 ∈ U

theorem Atlas.values_eq_ordered {h degree : ℝ} {N Δ : ℕ} (A : Atlas h N Δ)
    {U : Set Plane} {f : Scalar} (H : A.OverlapLaw U degree f)
    {z : Point} {n m : ℕ} (hn : A.Valid U z n) (hm : A.Valid U z m)
    (hi : A.index n ≤ A.index m) :
    ChartScales.Q n ^ (-degree) * f n (A.chart n z) =
      ChartScales.Q m ^ (-degree) * f m (A.chart m z) := by
  let k := A.index m - A.index n
  have hk : A.index n + k = A.index m := Nat.add_sub_of_le hi
  have hc := bandChart_chart A n m k hk z
  have hx : (A.chart n z).2.1 ∈ overlap h U n m := by
    refine ⟨hn.2.2, ?_⟩
    change (bandChartEquiv h n m k (A.chart n z)).2.1 ∈ U
    rw [hc]
    exact hm.2.2
  rw [H n hn.1 m hm.1 k hk _ hx, hc, ← mul_assoc, power_scale_cancel]

theorem Atlas.values_eq {h degree : ℝ} {N Δ : ℕ} (A : Atlas h N Δ)
    {U : Set Plane} {f : Scalar} (H : A.OverlapLaw U degree f)
    {z : Point} {n m : ℕ} (hn : A.Valid U z n) (hm : A.Valid U z m) :
    ChartScales.Q n ^ (-degree) * f n (A.chart n z) =
      ChartScales.Q m ^ (-degree) * f m (A.chart m z) := by
  rcases le_total (A.index n) (A.index m) with hi | hi
  · exact A.values_eq_ordered H hn hm hi
  · exact (A.values_eq_ordered H hm hn hi).symm

/-- Physical, choosing the witness provided by `hz`. -/
noncomputable def Atlas.physical {h : ℝ} {N Δ : ℕ} (A : Atlas h N Δ)
    (U : Set Plane) (degree : ℝ) (f : Scalar) (z : Point) : ℝ := by
  classical
  exact if hz : ∃ n, A.Valid U z n then
    ChartScales.Q (Classical.choose hz) ^ (-degree) *
      f (Classical.choose hz) (A.chart (Classical.choose hz) z)
  else 0

theorem Atlas.physical_eq {h degree : ℝ} {N Δ : ℕ} (A : Atlas h N Δ)
    {U : Set Plane} {f : Scalar} (H : A.OverlapLaw U degree f)
    {z : Point} {n : ℕ} (hn : A.Valid U z n) :
    A.physical U degree f z = ChartScales.Q n ^ (-degree) * f n (A.chart n z) := by
  classical
  have hz : ∃ n, A.Valid U z n := ⟨n, hn⟩
  rw [Atlas.physical, dite_eq_left hz]
  exact A.values_eq H (Classical.choose_spec hz) hn

/-- The physical field is constructed from overlapping valid bands. No
reference band is evaluated outside its original slow strip. -/
noncomputable def Atlas.family {h degree : ℝ} {N Δ : ℕ} (A : Atlas h N Δ)
    {U : Set Plane} {f : Scalar} (H : A.OverlapLaw U degree f) :
    PhysicalMeanJetBounds.CoherentFamily h degree N Δ U ℝ where
  native := f
  physical := A.physical U degree f
  gap := A.gap
  gap_le := A.gap_le
  gap_native n _ := Nat.sub_le _ _
  coherent := by
    intro n hn z ht hu
    rw [A.index_eq hn] at hu ⊢
    exact A.physical_eq H ⟨hn, ht, hu⟩

/-! ## Extracting scalar families from actual state overlap -/

/-- State overlap as an element of `Prop`. -/
def Atlas.StateOverlap {h : ℝ} {N Δ : ℕ} (A : Atlas h N Δ)
    (U : Set Plane) (u : CorrectionState.State Point) : Prop :=
  ∀ n ≥ N, ∀ m ≥ N, ∀ k, A.index n + k = A.index m →
    StateOn (PhysicalMeanDomain.slowDomain (overlap h U n m))
      (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m) u u n m

theorem Atlas.StateOverlap.radial {h : ℝ} {N Δ : ℕ} {A : Atlas h N Δ}
    {U : Set Plane} {u : CorrectionState.State Point} (H : A.StateOverlap U u) :
    A.OverlapLaw U (CoordinateAlgebra.A h) u.mean.radial := by
  intro n hn m hm k hk x hx
  exact (H n hn m hm k hk).mean.radial x hx

theorem Atlas.StateOverlap.angular {h : ℝ} {N Δ : ℕ} {A : Atlas h N Δ}
    {U : Set Plane} {u : CorrectionState.State Point} (H : A.StateOverlap U u) :
    A.OverlapLaw U (CoordinateAlgebra.A h) u.mean.angular := by
  intro n hn m hm k hk x hx
  exact (H n hn m hm k hk).mean.angular x hx

theorem Atlas.StateOverlap.axial {h : ℝ} {N Δ : ℕ} {A : Atlas h N Δ}
    {U : Set Plane} {u : CorrectionState.State Point} (H : A.StateOverlap U u) :
    A.OverlapLaw U (CoordinateAlgebra.A h) u.mean.axial := by
  intro n hn m hm k hk x hx
  exact (H n hn m hm k hk).mean.axial x hx

theorem velocityScale_square (h : ℝ) (n m : ℕ) :
    bandVelocityScale h n m * bandVelocityScale h n m =
      (ChartScales.Q n / ChartScales.Q m) ^ (2 * CoordinateAlgebra.A h) := by
  unfold bandVelocityScale
  rw [← Real.rpow_add (div_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m)), two_mul]

theorem Atlas.StateOverlap.pressure {h : ℝ} {N Δ : ℕ} {A : Atlas h N Δ}
    {U : Set Plane} {u : CorrectionState.State Point} (H : A.StateOverlap U u) :
    A.OverlapLaw U (2 * CoordinateAlgebra.A h) u.pressure := by
  intro n hn m hm k hk x hx
  simpa only [velocityScale_square] using (H n hn m hm k hk).pressure x hx

/-- Radial family, given by `A.family H.radial`. -/
noncomputable def Atlas.radialFamily {h : ℝ} {N Δ : ℕ} (A : Atlas h N Δ)
    {U : Set Plane} {u : CorrectionState.State Point} (H : A.StateOverlap U u) := A.family H.radial

/-- Angular family, given by `A.family H.angular`. -/
noncomputable def Atlas.angularFamily {h : ℝ} {N Δ : ℕ} (A : Atlas h N Δ)
    {U : Set Plane} {u : CorrectionState.State Point} (H : A.StateOverlap U u) := A.family H.angular

/-- Axial family, given by `A.family H.axial`. -/
noncomputable def Atlas.axialFamily {h : ℝ} {N Δ : ℕ} (A : Atlas h N Δ)
    {U : Set Plane} {u : CorrectionState.State Point} (H : A.StateOverlap U u) := A.family H.axial

/-- Pressure family, given by `A.family H.pressure /-! ## The literal initialized mean and
pressure -/ open CorrectionInitialization.ActualPrimary`. -/
noncomputable def Atlas.pressureFamily {h : ℝ} {N Δ : ℕ} (A : Atlas h N Δ)
    {U : Set Plane} {u : CorrectionState.State Point} (H : A.StateOverlap U u) := A.family
        H.pressure

/-! ## The literal initialized mean and pressure -/

open CorrectionInitialization.ActualPrimary

/-- Initial atlas, given by `commonAtlas h outgoing.data.h_pos.le N`. -/
noncomputable def initialAtlas (N : ℕ) := commonAtlas h outgoing.data.h_pos.le N

theorem initialized_overlap (B N0 N : ℕ) :
    (initialAtlas N).StateOverlap standardRegion.carrier (ActualInitialCoherence.initialized B N0)
        := by
  intro n hn m hm k hk
  exact ActualInitialCoherence.initialized_on_overlap B N0 n m k hk

/-- Initial radial family, given by `(initialAtlas N).radialFamily (initialized_overlap B N0
N)`. -/
noncomputable def initialRadialFamily (B N0 N : ℕ) :=
  (initialAtlas N).radialFamily (initialized_overlap B N0 N)

/-- Initial angular family, given by `(initialAtlas N).angularFamily (initialized_overlap B N0
N)`. -/
noncomputable def initialAngularFamily (B N0 N : ℕ) :=
  (initialAtlas N).angularFamily (initialized_overlap B N0 N)

/-- Initial axial family, given by `(initialAtlas N).axialFamily (initialized_overlap B N0 N)`. -/
noncomputable def initialAxialFamily (B N0 N : ℕ) :=
  (initialAtlas N).axialFamily (initialized_overlap B N0 N)

/-- Initial pressure family, given by `(initialAtlas N).pressureFamily (initialized_overlap B N0
N)`. -/
noncomputable def initialPressureFamily (B N0 N : ℕ) :=
  (initialAtlas N).pressureFamily (initialized_overlap B N0 N)

theorem initial_mean_moving (B N0 : ℕ) :
    MeanStateRegularity.MovingTriple standardRegion commonGauge.radial.inner
        commonGauge.radial.outer
      (ActualInitialCoherence.initialized B N0).mean :=
  (ActualInitialCoherence.initialized_primitive B N0).mean

theorem initial_pressure_moving (B N0 : ℕ) :
    GaugeMomentBalances.MovingField standardRegion commonGauge.radial.inner commonGauge.radial.outer
      (ActualInitialCoherence.initialized B N0).pressure :=
  (ActualInitialCoherence.initialized_primitive B N0).pressure
    (PrimaryTargetBounds.leftRadius_pos nominal)
    (ChartScales.radialExponent_pos h outgoing.data.h_pos.le) commonGauge_length
    (congrArg (fun s : CorrectionState.State Point => s.pressure)
      (ActualInitialCoherence.initialized_reconstructed B N0))

/-! ## Native classes supply the jets; no physical estimate is an input -/

theorem slowScale_le_S {n : ℕ} (hn : 1 ≤ n) :
    BaseContextAssembly.slowScale n ≤ ChartScales.S n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold BaseContextAssembly.slowScale
  apply max_le
  · dsimp [ChartScales.S]
    nlinarith
  · exact le_rfl

theorem initial_nativeJets_of_class {α : ℝ} {f : Scalar}
    (H : GaugeMomentBalances.MovingField standardRegion commonGauge.radial.inner
        commonGauge.radial.outer f)
    (hc : WeightedClasses.MeanClass ActualInitialMean.strip α f)
    (N : ℕ) (hN : 1 ≤ N) :
    PhysicalMeanJetBounds.NativeJets N standardRegion.carrier (h * α) f := by
  apply PhysicalMeanJetBounds.NativeJets.of_movingMeanClass standardRegion
    (PrimaryTargetBounds.leftRadius_pos nominal)
    (div_pos (FinalSlowBase.edgeExponent_pos nominal) (by norm_num)) zero_lt_one
    (ChartScales.epsilon h) BaseContextAssembly.slowScale (ChartScales.epsilon_pos h)
    (ChartScales.epsilon_le_one h outgoing.data.h_pos.le) BaseContextAssembly.one_le_slowScale
    H.smooth H.supported hc N (fun _ _ => rfl) (C := 1) (p := 1) le_rfl
  intro n hn
  simpa only [one_mul, pow_one] using slowScale_le_S (hN.trans hn)

theorem initialRadial_nativeJets (B N0 N : ℕ) (hN : 1 ≤ N) :
    PhysicalMeanJetBounds.NativeJets N standardRegion.carrier (h * (19 / 10))
      (initialRadialFamily B N0 N).native :=
  initial_nativeJets_of_class (initial_mean_moving B N0).radial
    (ActualInitialMean.initial_cumulative_bounds B N0).velocity.radial N hN

theorem initialAngular_nativeJets (B N0 N : ℕ) (hN : 1 ≤ N) :
    PhysicalMeanJetBounds.NativeJets N standardRegion.carrier (h * (9 / 10))
      (initialAngularFamily B N0 N).native :=
  initial_nativeJets_of_class (initial_mean_moving B N0).angular
    (ActualInitialMean.initial_cumulative_bounds B N0).velocity.angular N hN

theorem initialAxial_nativeJets (B N0 N : ℕ) (hN : 1 ≤ N) :
    PhysicalMeanJetBounds.NativeJets N standardRegion.carrier (h * (9 / 10))
      (initialAxialFamily B N0 N).native :=
  initial_nativeJets_of_class (initial_mean_moving B N0).axial
    (ActualInitialMean.initial_cumulative_bounds B N0).velocity.axial N hN

theorem initialPressure_nativeJets (B N0 N : ℕ) (hN : 1 ≤ N) :
    PhysicalMeanJetBounds.NativeJets N standardRegion.carrier (h * (9 / 10))
      (initialPressureFamily B N0 N).native :=
  initial_nativeJets_of_class (initial_pressure_moving B N0)
    (ActualInitialMean.initial_cumulative_bounds B N0).pressure N hN

theorem initialAngular_field_eq (B N0 N n : ℕ) (hn : N ≤ n) {w : SpaceTime}
    (ht : w ∈ PhysicalWaveSum.preterminal)
    (hu : (PhysicalMeanJetBounds.graph h n ((initialAtlas N).gap n) w).2.1 ∈
        standardRegion.carrier) :
    (initialAngularFamily B N0 N).field w = ChartScales.Q n ^ (-CoordinateAlgebra.A h) *
      (ActualInitialCoherence.initialized B N0).mean.angular n
        (PhysicalMeanJetBounds.graph h n ((initialAtlas N).gap n) w) :=
  (initialAngularFamily B N0 N).field_eq n hn ht hu

theorem initialPressure_field_eq (B N0 N n : ℕ) (hn : N ≤ n) {w : SpaceTime}
    (ht : w ∈ PhysicalWaveSum.preterminal)
    (hu : (PhysicalMeanJetBounds.graph h n ((initialAtlas N).gap n) w).2.1 ∈
        standardRegion.carrier) :
    (initialPressureFamily B N0 N).field w = ChartScales.Q n ^ (-(2 * CoordinateAlgebra.A h)) *
      (ActualInitialCoherence.initialized B N0).pressure n
        (PhysicalMeanJetBounds.graph h n ((initialAtlas N).gap n) w) :=
  (initialPressureFamily B N0 N).field_eq n hn ht hu

/-! ## Scalar stream overlap from the actual primitive operators -/

/-- Context overlap as an element of `Prop`. -/
def Atlas.ContextOverlap {h : ℝ} {N Δ : ℕ} (A : Atlas h N Δ)
    (U : Set Plane) (c : CorrectionState.Context Point) : Prop :=
  ∀ n ≥ N, ∀ m ≥ N, ∀ k, A.index n + k = A.index m →
    ContextOn (PhysicalMeanDomain.slowDomain (overlap h U n m))
      (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m) c c n m

/-- Gauge overlap as an element of `Prop`. -/
def Atlas.GaugeOverlap {h : ℝ} {N Δ : ℕ} (A : Atlas h N Δ)
    (U : Set Plane) (g : VariableGaugeMean.GaugeData Plane) : Prop :=
  ∀ n ≥ N, ∀ m ≥ N, ∀ k, A.index n + k = A.index m →
    GaugeOn (overlap h U n m) (bandScale n m) (bandSlowEquiv h n m).toContinuousLinearMap k g g n m

theorem streamScale (h : ℝ) (n m : ℕ) :
    bandVelocityScale h n m / bandScale n m =
      (ChartScales.Q n / ChartScales.Q m) ^ (CoordinateAlgebra.A h - 1 / 2) := by
  rw [Real.rpow_sub (div_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m))]
  rfl

theorem temporalPotential_moving {coord : ℝ} (U : LocalSignedRequest.SlowRegion coord)
    (g : VariableGaugeMean.GaugeData Plane) (c : CorrectionState.Context Point)
    (u : CorrectionState.State Point)
    (HP : MeanStateRegularity.PrimitiveData U g.radial.inner g.radial.outer c u)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hell : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (hfixed : (VariableGaugeMean.reconstructState g c u).pressure = u.pressure)
    (h : ℝ) (index : ℕ → ℕ) :
    GaugeMomentBalances.MovingField U g.radial.inner g.radial.outer
      (VariableGaugeMean.temporalPotential g h index c u) := by
  have Hz := MeanStageRegularity.MovingField.temporalAtIndex
    (HP.axial_reconstructed ha hd hell hfixed) h index
  convert! MeanStageRegularity.MovingField.streamPotential Hz ha g.radial.inner_lt_outer
    hd g.radial.frequency g.radial.radialDirection using 1
  funext n x
  simp only [VariableGaugeMean.temporalPotential, hell]

theorem Atlas.temporal_overlap {h : ℝ} {N Δ : ℕ} (A : Atlas h N Δ)
    (U : LocalSignedRequest.SlowRegion (2 * h))
    (g : VariableGaugeMean.GaugeData Plane) (c : CorrectionState.Context Point)
    (u : CorrectionState.State Point)
    (HC : A.ContextOverlap U.carrier c) (HS : A.StateOverlap U.carrier u)
    (HG : A.GaugeOverlap U.carrier g)
    (HP : MeanStateRegularity.PrimitiveData U g.radial.inner g.radial.outer c u)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hell : ∀ n, g.length n = VariableGaugeMean.qLength (2 * h))
    (hfixed : (VariableGaugeMean.reconstructState g c u).pressure = u.pressure) :
    A.OverlapLaw U.carrier (CoordinateAlgebra.A h - 1 / 2)
      (VariableGaugeMean.temporalPotential g h A.index c u) := by
  intro n hn m hm k hk x hx
  have Hz := HP.axial_reconstructed ha hd hell hfixed
  have Hs : VariableGaugeMean.SupportedGauge g.radial.inner g.radial.outer (g.length m)
      U.carrier (u.axialResidual c m) := by
    rw [hell]
    exact Hz.supported m
  have Ht := TemporalStateCoherence.temporalPotential_on (bandScale_pos n m) (bandSlowEquiv h n m) k
    (overlap_open h U.isOpen n m) U.isOpen (fun _ hx => hx.2) g g c c u u h A.index A.index
    n m ha hd (HG n hn m hm k hk) (HS n hn m hm k hk) (HC n hn m hm k hk)
    (TemporalStateCoherence.clock_band_transport h n m _ _ k hk)
    (Hz.smooth m) (Hz.periodic m) Hs
  have he := Ht x hx
  simp only [streamScale] at he ⊢
  exact he

theorem rankPotential_moving {coord : ℝ} (U : LocalSignedRequest.SlowRegion coord)
    (g : VariableGaugeMean.GaugeData Plane) (r : CorrectionState.RankData Plane)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point)
    (HG : LocalRankDefect.RankGeometry g r U.carrier c u)
    (hell : ∀ n, g.length n = VariableGaugeMean.qLength coord) :
    GaugeMomentBalances.MovingField U g.radial.inner g.radial.outer
      (VariableGaugeMean.rankPotential g r c u) := by
  have HD := MeanStageRegularity.rankDesired_moving HG hell
  convert! MeanStageRegularity.MovingField.streamPotential HD HG.primitive_inner_pos
    g.radial.inner_lt_outer HG.exponent_pos g.radial.frequency g.radial.radialDirection using 1
  funext n x
  simp only [VariableGaugeMean.rankPotential, hell]

/-- Rank overlap as an element of `Prop`. -/
def Atlas.RankOverlap {h : ℝ} {N Δ : ℕ} (_A : Atlas h N Δ)
    (U : Set Plane) (r : CorrectionState.RankData Plane) : Prop :=
  ∀ n ≥ N, ∀ m ≥ N, RankStateCoherence.RankOn (overlap h U n m) (bandSlowEquiv h n m)
    (bandScale n m) (bandVelocityScale h n m) r r n m

theorem Atlas.rank_overlap {h : ℝ} {N Δ : ℕ} (A : Atlas h N Δ)
    (U : LocalSignedRequest.SlowRegion (2 * h))
    (g : VariableGaugeMean.GaugeData Plane) (r : CorrectionState.RankData Plane)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point)
    (HC : A.ContextOverlap U.carrier c) (HS : A.StateOverlap U.carrier u)
    (HG : A.GaugeOverlap U.carrier g) (HR : A.RankOverlap U.carrier r)
    (HP : MeanStateRegularity.PrimitiveData U g.radial.inner g.radial.outer c u)
    (HF : LocalRankDefect.RankGeometry g r U.carrier c u) :
    A.OverlapLaw U.carrier (CoordinateAlgebra.A h - 1 / 2)
      (VariableGaugeMean.rankPotential g r c u) := by
  intro n hn m hm k hk x hx
  have Hd := CycleStateCoherence.debtRegular_of_primitive HP HF.primitive_inner_pos
      g.radial.inner_lt_outer m
  have Hp := RankStateCoherence.rankPotential_on (bandScale_pos n m)
    (Real.rpow_pos_of_pos (div_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m)) _).ne'
    (bandSlowEquiv h n m) k (overlap_open h U.isOpen n m) U.isOpen (fun _ hx => hx.2)
    (HS n hn m hm k hk) (HC n hn m hm k hk) Hd (HR n hn m hm) (HG n hn m hm k hk) HF
  have he := Hp x hx
  simp only [ bandScale,
    ← Real.rpow_sub (div_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m))] at he ⊢
  exact he

/-! ## The actual initial temporal and rank streams -/

theorem initial_context_overlap (B N : ℕ) :
    (initialAtlas N).ContextOverlap standardRegion.carrier (commonContext B) := by
  intro n hn m hm k hk
  exact ActualInitialCoherence.context_band B
    (fun s hs => standardRegion.time_pos s hs.1) n m k hk

theorem initial_gauge_overlap (N : ℕ) :
    (initialAtlas N).GaugeOverlap standardRegion.carrier commonGauge := by
  intro n hn m hm k hk
  exact ActualInitialCoherence.commonGauge_on
    (fun s hs => standardRegion.time_pos s hs.1) n m k hk

theorem initial_rank_overlap (N : ℕ) :
    (initialAtlas N).RankOverlap standardRegion.carrier rankData := by
  intro n hn m hm
  exact RankStateCoherence.normalized_rank_on outgoing.data.h_pos outgoing.data.h_lt_half
    rankAmplitude outgoing.data.core.lam rankInner rankOuter n m
    (fun s hs => standardRegion.time_pos s hs.1)

theorem initial_primary_overlap (B N0 N : ℕ) :
    (initialAtlas N).StateOverlap standardRegion.carrier (ActualInitialCoherence.primary B N0) := by
  intro n hn m hm k hk
  exact ActualInitialCoherence.primary_band_of_seed B N0 n m k hk
    (overlap_open h standardRegion.isOpen n m) inter_subset_left (fun _ hx => hx.2)
    (ActualInitialCoherence.seed_primitive B N0)
    (ActualInitialCoherence.seed_band B N0 n m k hk inter_subset_left (fun _ hx => hx.2))

theorem initial_temporalState_overlap (B N0 N : ℕ) :
    (initialAtlas N).StateOverlap standardRegion.carrier (ActualInitialCoherence.temporal B N0) :=
        by
  intro n hn m hm k hk
  exact ActualInitialCoherence.temporal_band_of_seed B N0 n m k hk
    (overlap_open h standardRegion.isOpen n m) inter_subset_left (fun _ hx => hx.2)
    (ActualInitialCoherence.seed_primitive B N0)
    (ActualInitialCoherence.seed_band B N0 n m k hk inter_subset_left (fun _ hx => hx.2))

/-- Initial temporal scalar, constructed using `VariableGaugeMean.temporalPotential`. -/
noncomputable def initialTemporalScalar (B N0 : ℕ) : Scalar :=
  VariableGaugeMean.temporalPotential commonGauge h (CorrectionInitialization.CommonWindow.index h)
    (commonContext B) (ActualInitialCoherence.primary B N0)

/-- Initial rank scalar, given by `VariableGaugeMean.rankPotential commonGauge rankData
(commonContext B) (ActualInitialCoherence.temporal B N0)`. -/
noncomputable def initialRankScalar (B N0 : ℕ) : Scalar :=
  VariableGaugeMean.rankPotential commonGauge rankData (commonContext B)
      (ActualInitialCoherence.temporal B N0)

theorem initialTemporal_overlap (B N0 N : ℕ) :
    (initialAtlas N).OverlapLaw standardRegion.carrier (CoordinateAlgebra.A h - 1 / 2)
      (initialTemporalScalar B N0) :=
  (initialAtlas N).temporal_overlap standardRegion commonGauge (commonContext B)
    (ActualInitialCoherence.primary B N0) (initial_context_overlap B N) (initial_primary_overlap B
        N0 N)
    (initial_gauge_overlap N) (ActualInitialCoherence.primary_primitive B N0)
    (PrimaryTargetBounds.leftRadius_pos nominal)
    (ChartScales.radialExponent_pos h outgoing.data.h_pos.le) commonGauge_length rfl

theorem initialRank_overlap (B N0 N : ℕ) :
    (initialAtlas N).OverlapLaw standardRegion.carrier (CoordinateAlgebra.A h - 1 / 2)
      (initialRankScalar B N0) :=
  (initialAtlas N).rank_overlap standardRegion commonGauge rankData (commonContext B)
    (ActualInitialCoherence.temporal B N0) (initial_context_overlap B N)
        (initial_temporalState_overlap B N0 N)
    (initial_gauge_overlap N) (initial_rank_overlap N) (ActualInitialCoherence.temporal_primitive B
        N0)
    (ActualInitialCoherence.rank_geometry_of_primitive B _
        (ActualInitialCoherence.temporal_primitive B N0))

/-- Initial temporal family, given by `(initialAtlas N).family (initialTemporal_overlap B N0
N)`. -/
noncomputable def initialTemporalFamily (B N0 N : ℕ) :=
  (initialAtlas N).family (initialTemporal_overlap B N0 N)

/-- Initial rank family, given by `(initialAtlas N).family (initialRank_overlap B N0 N)`. -/
noncomputable def initialRankFamily (B N0 N : ℕ) :=
  (initialAtlas N).family (initialRank_overlap B N0 N)

theorem initialTemporal_moving (B N0 : ℕ) :
    GaugeMomentBalances.MovingField standardRegion commonGauge.radial.inner commonGauge.radial.outer
      (initialTemporalScalar B N0) :=
  temporalPotential_moving standardRegion commonGauge (commonContext B)
      (ActualInitialCoherence.primary B N0)
    (ActualInitialCoherence.primary_primitive B N0) (PrimaryTargetBounds.leftRadius_pos nominal)
    (ChartScales.radialExponent_pos h outgoing.data.h_pos.le) commonGauge_length rfl h
    (CorrectionInitialization.CommonWindow.index h)

theorem initialRank_moving (B N0 : ℕ) :
    GaugeMomentBalances.MovingField standardRegion commonGauge.radial.inner commonGauge.radial.outer
      (initialRankScalar B N0) :=
  rankPotential_moving standardRegion commonGauge rankData (commonContext B)
      (ActualInitialCoherence.temporal B N0)
    (ActualInitialCoherence.rank_geometry_of_primitive B _
        (ActualInitialCoherence.temporal_primitive B N0))
    commonGauge_length

/-! ## Stream classes derived from the actual sources -/

theorem rankPotential_class {coord A0 B0 α cL cR : ℝ}
    (U : LocalSignedRequest.SlowRegion coord)
    (g : VariableGaugeMean.GaugeData Plane) (r : CorrectionState.RankData Plane)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point)
    (ha : 0 < g.radial.inner) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε L : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hL : ∀ n, 1 ≤ L n)
    (HG : LocalRankDefect.RankGeometry g r U.carrier c u)
    (HP : RankStateBounds.NormalizedParameters coord A0 B0 r U.carrier) (hB : B0 ≠ 0)
    (hleft : g.radial.inner < r.inner) (hright : r.outer < g.radial.outer)
    (HD : WeightedClasses.UnweightedClass
      (PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen ε L hε hεone hL)
      α (CorrectionState.debt c u)) :
    WeightedClasses.MeanClass
      (LocalSignedRequest.movingStripData U g.radial.inner g.radial.outer cL cR ha hcL hcR ε L hε
          hεone hL)
      α (VariableGaugeMean.rankPotential g r c u) := by
  obtain ⟨lo, hi, hlo, horder, hlo', hhi', hlow, hupp⟩ :=
    RankStateBounds.containingShell U HG.inner_pos HG.inner_lt_outer
  have hlow' (n : ℕ) (x : Plane) (hx : x ∈ U.carrier) : lo ≤ r.length n x * r.inner := by
    rw [HP.length n x hx]
    exact hlow x hx
  have hupp' (n : ℕ) (x : Plane) (hx : x ∈ U.carrier) : r.length n x * r.outer ≤ hi := by
    rw [HP.length n x hx]
    exact hupp x hx
  have Hsource := (RankStateBounds.rankSources_fixedClass U HG HP hB hlo hcL hcR
    hlo' hhi' ε L hε hεone hL HD).2
  have Hfixed := LocalRankDefect.RankGeometry.potential_class hlo horder hcL hcR
    ε L hε hεone hL U.carrier U.isOpen HG hlow' hupp' Hsource
  have Hlocal := HG.potential_localShell hlo horder U.isOpen hlow' hupp'
  have Hsupport (n : ℕ) : VariableGaugeMean.SupportedGauge r.inner r.outer
      (VariableGaugeMean.qLength coord) U.carrier (VariableGaugeMean.rankPotential g r c u n) := by
    intro z hz hne
    have Hs := HG.potential_supportedGauge n z hz hne
    simpa only [HP.length n _ hz] using Hs
  exact RankStateBounds.fixedClass_to_moving U ha hlo hcL hcR ε L hε hεone hL
    hleft hright Hlocal Hsupport Hfixed

theorem initialTemporal_class (B N0 : ℕ) :
    WeightedClasses.MeanClass ActualInitialMean.strip (1 - ChartScales.kappa)
        (initialTemporalScalar B N0) := by
  have Hz := (ActualInitialCoherence.primary_primitive B N0).axial_reconstructed
    (PrimaryTargetBounds.leftRadius_pos nominal)
    (ChartScales.radialExponent_pos h outgoing.data.h_pos.le) commonGauge_length rfl
  have Hc := (ActualInitialMean.primary_bounds B N0).2.2.2.1
  have Hp := VariableGaugeMean.meanClass_temporalStreamPotential standardRegion
    (PrimaryTargetBounds.leftRadius_pos nominal) (PrimaryTargetBounds.radii_ordered nominal)
    (ChartScales.radialExponent_pos h outgoing.data.h_pos.le)
    (div_pos (FinalSlowBase.edgeExponent_pos nominal) (by norm_num)) zero_lt_one
    (ChartScales.epsilon h) BaseContextAssembly.slowScale (ChartScales.epsilon_pos h)
    (ChartScales.epsilon_le_one h outgoing.data.h_pos.le) BaseContextAssembly.one_le_slowScale
    outgoing.data.h_pos.le (fun n => le_max_right 1 (ChartScales.S n))
    (CorrectionInitialization.CommonWindow.index h) (CorrectionInitialization.CommonWindow.gap h)
    (CorrectionInitialization.CommonWindow.native_le_index_add h outgoing.data.h_pos.le)
    Hz.smooth Hz.periodic Hz.supported Hc commonGauge.radial.frequency
    (fun _ => commonGauge.radial.radialDirection)
  convert! Hp using 1

theorem initialRank_class (B N0 : ℕ) :
    WeightedClasses.MeanClass ActualInitialMean.strip (1 - ChartScales.kappa) (initialRankScalar B
        N0) := by
  have HD := (ActualInitialMean.primary_mean_data B N0).temporal_debt_bounds
    (ActualInitialMean.temporal_bounds B N0)
  exact rankPotential_class standardRegion commonGauge rankData (commonContext B)
    (ActualInitialCoherence.temporal B N0) (PrimaryTargetBounds.leftRadius_pos nominal)
    (div_pos (FinalSlowBase.edgeExponent_pos nominal) (by norm_num)) zero_lt_one
    (ChartScales.epsilon h) BaseContextAssembly.slowScale (ChartScales.epsilon_pos h)
    (ChartScales.epsilon_le_one h outgoing.data.h_pos.le) BaseContextAssembly.one_le_slowScale
    (ActualInitialCoherence.rank_geometry_of_primitive B _
        (ActualInitialCoherence.temporal_primitive B N0))
    (rankData_parameters standardRegion.carrier) rankAmplitude_pos.ne'
    active_left_before_rank rank_before_active_right HD

theorem initialTemporal_nativeJets (B N0 N : ℕ) (hN : 1 ≤ N) :
    PhysicalMeanJetBounds.NativeJets N standardRegion.carrier (h * (1 - ChartScales.kappa))
      (initialTemporalFamily B N0 N).native :=
  initial_nativeJets_of_class (initialTemporal_moving B N0) (initialTemporal_class B N0) N hN

theorem initialRank_nativeJets (B N0 N : ℕ) (hN : 1 ≤ N) :
    PhysicalMeanJetBounds.NativeJets N standardRegion.carrier (h * (1 - ChartScales.kappa))
      (initialRankFamily B N0 N).native :=
  initial_nativeJets_of_class (initialRank_moving B N0) (initialRank_class B N0) N hN

/-! ## One atlas for the literal correction recurrence -/

open CorrectionStep CorrectionState

/-- The inputs are the seed and the two actual wave insertions per cycle.
Mean and pressure overlap at later states is proved from these data. -/
structure CycleData {ι : Type} (G : CycleStateCoherence.Geometry) (N Δ : ℕ)
    (p : ℕ → CycleParameters ι) (c : Context Point) (seed : CycleState ι)
    (U : LocalSignedRequest.SlowRegion (2 * G.h)) where
  /-- Atlas of `CycleData`, of type `Atlas G.h N Δ`. -/
  atlas : Atlas G.h N Δ
  index_eq : atlas.index = G.index
  realizes : ∀ j, CycleStateCoherence.Realizes G (p j) c
  context : atlas.ContextOverlap U.carrier c
  seed_state : atlas.StateOverlap U.carrier seed.state
  seed_axis : ∀ n ≥ N, ∀ m ≥ N, ∀ k, atlas.index n + k = atlas.index m →
    CycleStateCoherence.AxisBand G (overlap G.h U.carrier n m) n m k seed.axisymmetricAlias
  primitive : MeanStateRegularity.PrimitiveData U G.inner G.outer c seed.state
  rank : LocalRankDefect.RankGeometry G.gauge G.rank U.carrier c seed.state
  covariance_particular : ∀ j,
    let x := CycleState.iterate p c seed j
    ∀ i l, GaugeMomentBalances.MovingField U G.inner G.outer
      (SignedMeanGain.covarianceIncrement x.state.oscillation
        ((p j).particularVelocity x.coefficients c x.state) i l)
  covariance_signed : ∀ j,
    let x := CycleState.iterate p c seed j
    ∀ i l, GaugeMomentBalances.MovingField U G.inner G.outer
      (SignedMeanGain.covarianceIncrement ((p j).afterParticular x.coefficients c
          x.state).oscillation
        ((p j).signedVelocity x.coefficients c x.state) i l)
  waves : ∀ n ≥ N, ∀ m ≥ N, ∀ k, atlas.index n + k = atlas.index m →
    ∀ j, let x := CycleState.iterate p c seed j
      CycleStateCoherence.CycleWavesOn G (p j) x.coefficients c x.state
        (overlap G.h U.carrier n m) n m k

namespace CycleData

variable {ι : Type} {G : CycleStateCoherence.Geometry} {N Δ : ℕ}
    {p : ℕ → CycleParameters ι} {c : Context Point} {seed : CycleState ι}
    {U : LocalSignedRequest.SlowRegion (2 * G.h)} (D : CycleData G N Δ p c seed U)

include D

theorem at_pair (n : ℕ) (hn : N ≤ n) (m : ℕ) (hm : N ≤ m) (k : ℕ)
    (hk : D.atlas.index n + k = D.atlas.index m) (j : ℕ) :
    CycleStateCoherence.StateBand G (overlap G.h U.carrier n m) n m k (CycleState.iterate p c seed
        j).state ∧
    CycleStateCoherence.AxisBand G (overlap G.h U.carrier n m) n m k (CycleState.iterate p c seed
        j).axisymmetricAlias ∧
    MeanStateRegularity.PrimitiveData U G.inner G.outer c (CycleState.iterate p c seed j).state :=
  CycleStateCoherence.iterate_state_axis G p c seed D.realizes
    (overlap_open G.h U.isOpen n m) inter_subset_left n m k
    (by simpa only [D.index_eq] using hk) (fun _ hx => hx.2)
    (D.context n hn m hm k hk) (D.seed_state n hn m hm k hk) (D.seed_axis n hn m hm k hk)
    D.primitive D.rank D.covariance_particular D.covariance_signed (D.waves n hn m hm k hk) j

theorem state_overlap (j : ℕ) :
    D.atlas.StateOverlap U.carrier (CycleState.iterate p c seed j).state :=
  fun n hn m hm k hk => (D.at_pair n hn m hm k hk j).1

theorem primitives (j : ℕ) :
    MeanStateRegularity.PrimitiveData U G.inner G.outer c (CycleState.iterate p c seed j).state :=
  (D.at_pair N le_rfl N le_rfl 0 (by simp) j).2.2

theorem inner_eq (j : ℕ) : (p j).gauge.radial.inner = G.inner := by
  rw [(D.realizes j).gauge]
  rfl

theorem outer_eq (j : ℕ) : (p j).gauge.radial.outer = G.outer := by
  rw [(D.realizes j).gauge]
  rfl

theorem rank_geometry (j : ℕ) :
    LocalRankDefect.RankGeometry (p j).gauge (p j).rank U.carrier c (CycleState.iterate p c seed
        j).state := by
  rw [(D.realizes j).gauge, (D.realizes j).rank]
  exact MeanStageRegularity.rankGeometry_for_state (D.primitives j) G.inner_pos G.inner_lt_outer
      D.rank

theorem stage_primitives (j : ℕ) :
    CycleStateCoherence.StagePrimitives G (p j) (CycleState.iterate p c seed j).coefficients c
      (CycleState.iterate p c seed j).state U := by
  apply CycleStateCoherence.stage_primitives (D.realizes j)
  · simpa only [D.inner_eq, D.outer_eq] using D.primitives j
  · simpa only [D.inner_eq, D.outer_eq] using D.covariance_particular j
  · simpa only [D.inner_eq, D.outer_eq] using D.covariance_signed j
  · exact D.rank_geometry j

theorem stage_transport (j : ℕ) (n : ℕ) (hn : N ≤ n) (m : ℕ) (hm : N ≤ m) (k : ℕ)
    (hk : D.atlas.index n + k = D.atlas.index m) :
    CycleStateCoherence.CycleTransport G (p j) (CycleState.iterate p c seed j).coefficients c
      (CycleState.iterate p c seed j).state (overlap G.h U.carrier n m) n m k := by
  apply CycleStateCoherence.cycle_transport (D.realizes j) (overlap_open G.h U.isOpen n m)
    inter_subset_left n m k (by simpa only [D.index_eq] using hk) (fun _ hx => hx.2)
    (D.context n hn m hm k hk) (D.state_overlap j n hn m hm k hk)
  · simpa only [D.inner_eq, D.outer_eq] using D.primitives j
  · simpa only [D.inner_eq, D.outer_eq] using D.covariance_particular j
  · simpa only [D.inner_eq, D.outer_eq] using D.covariance_signed j
  · exact D.rank_geometry j
  · exact D.waves n hn m hm k hk j

/-- Radial family, given by `D.atlas.radialFamily (D.state_overlap j)`. -/
noncomputable def radialFamily (j : ℕ) := D.atlas.radialFamily (D.state_overlap j)
/-- Angular family, given by `D.atlas.angularFamily (D.state_overlap j)`. -/
noncomputable def angularFamily (j : ℕ) := D.atlas.angularFamily (D.state_overlap j)
/-- Axial family, given by `D.atlas.axialFamily (D.state_overlap j)`. -/
noncomputable def axialFamily (j : ℕ) := D.atlas.axialFamily (D.state_overlap j)
/-- Pressure family, given by `D.atlas.pressureFamily (D.state_overlap j)`. -/
noncomputable def pressureFamily (j : ℕ) := D.atlas.pressureFamily (D.state_overlap j)

/-- Temporal scalar, constructed using `VariableGaugeMean.temporalPotential`. -/
noncomputable def temporalScalar (_D : CycleData G N Δ p c seed U) (j : ℕ) : Scalar :=
  VariableGaugeMean.temporalPotential (p j).gauge (p j).timeExponent (p j).commonIndex c
    ((p j).afterSigned (CycleState.iterate p c seed j).coefficients c (CycleState.iterate p c seed
        j).state)

/-- Rank scalar, constructed using `VariableGaugeMean.rankPotential`. -/
noncomputable def rankScalar (_D : CycleData G N Δ p c seed U) (j : ℕ) : Scalar :=
  VariableGaugeMean.rankPotential (p j).gauge (p j).rank c
    ((p j).afterTemporal (CycleState.iterate p c seed j).coefficients c (CycleState.iterate p c
        seed j).state)

theorem gauge_overlap (j : ℕ) : D.atlas.GaugeOverlap U.carrier (p j).gauge := by
  intro n hn m hm k hk
  exact (D.realizes j).gauge_on n m k (by simpa only [D.index_eq] using hk)
    (fun s hs => U.time_pos s hs.1)

theorem rank_overlap_data (j : ℕ) : D.atlas.RankOverlap U.carrier (p j).rank :=
  fun n _ m _ => (D.realizes j).rank_on n m (fun s hs => U.time_pos s hs.1)

theorem signed_overlap (j : ℕ) : D.atlas.StateOverlap U.carrier
    ((p j).afterSigned (CycleState.iterate p c seed j).coefficients c (CycleState.iterate p c seed
        j).state) :=
  fun n hn m hm k hk => (D.stage_transport j n hn m hm k hk).signed

theorem temporalState_overlap (j : ℕ) : D.atlas.StateOverlap U.carrier
    ((p j).afterTemporal (CycleState.iterate p c seed j).coefficients c (CycleState.iterate p c
        seed j).state) :=
  fun n hn m hm k hk => (D.stage_transport j n hn m hm k hk).temporal

theorem temporalScalar_overlap (j : ℕ) :
    D.atlas.OverlapLaw U.carrier (CoordinateAlgebra.A G.h - 1 / 2) (D.temporalScalar j) := by
  have H := D.atlas.temporal_overlap U (p j).gauge c _ D.context (D.signed_overlap j)
    (D.gauge_overlap j) (D.stage_primitives j).signed (D.realizes j).inner_pos
    (D.realizes j).exponent_pos (D.realizes j).length rfl
  simpa only [temporalScalar, (D.realizes j).timeExponent, (D.realizes j).index, D.index_eq] using H

theorem rankScalar_overlap (j : ℕ) :
    D.atlas.OverlapLaw U.carrier (CoordinateAlgebra.A G.h - 1 / 2) (D.rankScalar j) :=
  D.atlas.rank_overlap U (p j).gauge (p j).rank c _ D.context (D.temporalState_overlap j)
    (D.gauge_overlap j) (D.rank_overlap_data j) (D.stage_primitives j).temporal
    (D.stage_primitives j).rankGeometry

/-- Temporal family, given by `D.atlas.family (D.temporalScalar_overlap j)`. -/
noncomputable def temporalFamily (j : ℕ) := D.atlas.family (D.temporalScalar_overlap j)
/-- Rank family, given by `D.atlas.family (D.rankScalar_overlap j)`. -/
noncomputable def rankFamily (j : ℕ) := D.atlas.family (D.rankScalar_overlap j)

theorem temporal_moving (j : ℕ) :
    GaugeMomentBalances.MovingField U G.inner G.outer (D.temporalScalar j) := by
  have H := temporalPotential_moving U (p j).gauge c _ (D.stage_primitives j).signed
    (D.realizes j).inner_pos (D.realizes j).exponent_pos (D.realizes j).length rfl
    (p j).timeExponent (p j).commonIndex
  simp only [D.inner_eq, D.outer_eq] at H
  exact H

theorem rank_moving (j : ℕ) :
    GaugeMomentBalances.MovingField U G.inner G.outer (D.rankScalar j) := by
  have H := rankPotential_moving U (p j).gauge (p j).rank c _ (D.stage_primitives j).rankGeometry
    (D.realizes j).length
  simp only [D.inner_eq, D.outer_eq] at H
  exact H

theorem reconstructed
    (hseed : (VariableGaugeMean.reconstructState G.gauge c seed.state).pressure =
        seed.state.pressure)
    (j : ℕ) :
    (VariableGaugeMean.reconstructState G.gauge c (CycleState.iterate p c seed j).state).pressure =
      (CycleState.iterate p c seed j).state.pressure := by
  cases j with
  | zero => exact hseed
  | succ j =>
      have H := (p j).next_reconstructed (CycleState.iterate p c seed j).coefficients c
        (CycleState.iterate p c seed j).state
      simp only [(D.realizes j).gauge] at H
      exact H

theorem pressure_moving
    (hseed : (VariableGaugeMean.reconstructState G.gauge c seed.state).pressure =
        seed.state.pressure)
    (j : ℕ) :
    GaugeMomentBalances.MovingField U G.inner G.outer (CycleState.iterate p c seed
        j).state.pressure :=
  (D.primitives j).pressure G.inner_pos (ChartScales.radialExponent_pos G.h G.h_pos.le)
    (fun _ => rfl) (D.reconstructed hseed j)

end CycleData

/-! ## Concrete initialization of the overlap-preserving recurrence -/

/-- Initial geometry, bundling `h`, `inner`, `outer`, `frequency` and the required compatibility
proofs. -/
noncomputable def initialGeometry : CycleStateCoherence.Geometry where
  h := h
  inner := PrimaryTargetBounds.leftRadius nominal
  outer := PrimaryTargetBounds.rightRadius nominal
  frequency := 1
  rankAmplitude := rankAmplitude
  rankShape := outgoing.data.core.lam
  rankInner := rankInner
  rankOuter := rankOuter
  operatorInner := PrimaryTargetBounds.leftRadius nominal
  operatorOuter := PrimaryTargetBounds.rightRadius nominal
  index := CorrectionInitialization.CommonWindow.index h
  h_pos := outgoing.data.h_pos
  h_lt_half := outgoing.data.h_lt_half
  inner_pos := PrimaryTargetBounds.leftRadius_pos nominal
  inner_lt_outer := PrimaryTargetBounds.radii_ordered nominal
  operator_lt := PrimaryTargetBounds.radii_ordered nominal

theorem initialGeometry_gauge : initialGeometry.gauge = commonGauge :=
  ActualInitialCoherence.commonGauge_eq_similarity.symm

theorem initialGeometry_rank : initialGeometry.rank = rankData := rfl

theorem initial_realizes {ι : Type} (B : ℕ)
    (particular : ι → ParticularParameters CycleSlow)
    (signed : ι → PeriodizedSignedParameters CyclePoint TorusInverse.Frequency) :
    CycleStateCoherence.Realizes initialGeometry
      (CycleParameters.ofGeometry ActualInitialization.geometry h
        (CorrectionInitialization.CommonWindow.index h) ActualInitialization.axial particular
            signed rankData)
      (commonContext B) := by
  refine ⟨initialGeometry_gauge.symm, rfl, rfl, rfl, rfl, rfl⟩

/-- Only the actual wave insertions remain inputs. All seed overlap and
primitive regularity are supplied by the constructed initialization. -/
structure InitialCycleInput (B N0 N : ℕ)
    (p : ℕ → CycleParameters (ActualInitialization.Index B N0)) : Prop where
  realizes : ∀ j, CycleStateCoherence.Realizes initialGeometry (p j) (commonContext B)
  covariance_particular : ∀ j,
    let x := CycleState.iterate p (commonContext B)
      (ActualInitialization.initialCycleState B N0) j
    ∀ i l, GaugeMomentBalances.MovingField standardRegion commonGauge.radial.inner
        commonGauge.radial.outer
      (SignedMeanGain.covarianceIncrement x.state.oscillation
        ((p j).particularVelocity x.coefficients (commonContext B) x.state) i l)
  covariance_signed : ∀ j,
    let x := CycleState.iterate p (commonContext B)
      (ActualInitialization.initialCycleState B N0) j
    ∀ i l, GaugeMomentBalances.MovingField standardRegion commonGauge.radial.inner
        commonGauge.radial.outer
      (SignedMeanGain.covarianceIncrement ((p j).afterParticular x.coefficients (commonContext B)
          x.state).oscillation
        ((p j).signedVelocity x.coefficients (commonContext B) x.state) i l)
  waves : ∀ n ≥ N, ∀ m ≥ N, ∀ k,
    CorrectionInitialization.CommonWindow.index h n + k =
        CorrectionInitialization.CommonWindow.index h m →
    ∀ j,
      let x := CycleState.iterate p (commonContext B)
        (ActualInitialization.initialCycleState B N0) j
      CycleStateCoherence.CycleWavesOn initialGeometry (p j) x.coefficients (commonContext B)
          x.state
        (overlap h standardRegion.carrier n m) n m k

/-- Initial cycle data, bundling `atlas`, `index_eq`, `realizes`, `context` and the required
compatibility proofs. -/
noncomputable def initialCycleData {B N0 N : ℕ}
    {p : ℕ → CycleParameters (ActualInitialization.Index B N0)} (H : InitialCycleInput B N0 N p) :
    CycleData initialGeometry N (CorrectionInitialization.CommonWindow.gap h) p (commonContext B)
      (ActualInitialization.initialCycleState B N0) standardRegion where
  atlas := initialAtlas N
  index_eq := rfl
  realizes := H.realizes
  context := initial_context_overlap B N
  seed_state := initialized_overlap B N0 N
  seed_axis := by
    intro n hn m hm k hk x hx i
    have He := ActualInitialCoherence.initialized_alias_band B N0 n m k hk hx 0 i
    rw [ActualInitialCoherence.initialized_aliases] at He
    exact He
  primitive := ActualInitialCoherence.initialized_primitive B N0
  rank := by
    rw [initialGeometry_gauge, initialGeometry_rank]
    exact ActualInitialCoherence.rank_geometry_of_primitive B _
        (ActualInitialCoherence.initialized_primitive B N0)
  covariance_particular := H.covariance_particular
  covariance_signed := H.covariance_signed
  waves := H.waves

/-! ## The actual increments and their single physical representatives -/

theorem Atlas.OverlapLaw.add {h d : ℝ} {N Δ : ℕ} {A : Atlas h N Δ}
    {U : Set Plane} {f g : Scalar} (Hf : A.OverlapLaw U d f) (Hg : A.OverlapLaw U d g) :
    A.OverlapLaw U d (f + g) := by
  intro n hn m hm k hk x hx
  change f n x + g n x = _
  rw [Hf n hn m hm k hk x hx, Hg n hn m hm k hk x hx]
  exact (mul_add _ _ _).symm

theorem Atlas.OverlapLaw.sub {h d : ℝ} {N Δ : ℕ} {A : Atlas h N Δ}
    {U : Set Plane} {f g : Scalar} (Hf : A.OverlapLaw U d f) (Hg : A.OverlapLaw U d g) :
    A.OverlapLaw U d (f - g) := by
  intro n hn m hm k hk x hx
  change f n x - g n x = _
  rw [Hf n hn m hm k hk x hx, Hg n hn m hm k hk x hx]
  exact (mul_sub _ _ _).symm

theorem Atlas.physical_add {h : ℝ} {N Δ : ℕ} (A : Atlas h N Δ)
    (U : Set Plane) (d : ℝ) (f g : Scalar) :
    A.physical U d (f + g) = A.physical U d f + A.physical U d g := by
  classical
  funext z
  by_cases hz : ∃ n, A.Valid U z n
  · simp only [Atlas.physical, dite_eq_left hz, Pi.add_apply, mul_add]
  · simp only [Atlas.physical, dite_eq_right hz, Pi.add_apply, zero_add]

theorem Atlas.physical_sub {h : ℝ} {N Δ : ℕ} (A : Atlas h N Δ)
    (U : Set Plane) (d : ℝ) (f g : Scalar) :
    A.physical U d (f - g) = A.physical U d f - A.physical U d g := by
  classical
  funext z
  by_cases hz : ∃ n, A.Valid U z n
  · simp only [Atlas.physical, dite_eq_left hz, Pi.sub_apply, mul_sub]
  · simp only [Atlas.physical, dite_eq_right hz, Pi.sub_apply, sub_self]

/-- Initial stream family, given by `(initialAtlas N).family ((initialTemporal_overlap B N0
N).add (initialRank_overlap B N0 N))`. -/
noncomputable def initialStreamFamily (B N0 N : ℕ) :=
  (initialAtlas N).family ((initialTemporal_overlap B N0 N).add (initialRank_overlap B N0 N))

theorem initialStream_moving (B N0 : ℕ) :
    GaugeMomentBalances.MovingField standardRegion commonGauge.radial.inner commonGauge.radial.outer
      (initialTemporalScalar B N0 + initialRankScalar B N0) :=
  MeanStateRegularity.MovingField.add (initialTemporal_moving B N0) (initialRank_moving B N0)

theorem initialStream_nativeJets (B N0 N : ℕ) (hN : 1 ≤ N) :
    PhysicalMeanJetBounds.NativeJets N standardRegion.carrier (h * (1 - ChartScales.kappa))
      (initialStreamFamily B N0 N).native :=
  initial_nativeJets_of_class (initialStream_moving B N0)
    ((initialTemporal_class B N0).add (initialRank_class B N0)) N hN

namespace CycleData

variable {ι : Type} {G : CycleStateCoherence.Geometry} {N Δ : ℕ}
    {p : ℕ → CycleParameters ι} {c : Context Point} {seed : CycleState ι}
    {U : LocalSignedRequest.SlowRegion (2 * G.h)} (D : CycleData G N Δ p c seed U)

/-- Stream family, given by `D.atlas.family ((D.temporalScalar_overlap j).add
(D.rankScalar_overlap j))`. -/
noncomputable def streamFamily (j : ℕ) :=
  D.atlas.family ((D.temporalScalar_overlap j).add (D.rankScalar_overlap j))

/-- Angular increment family, given by `D.atlas.family (((D.state_overlap (j+1)).angular).sub
((D.state_overlap j).angular))`. -/
noncomputable def angularIncrementFamily (j : ℕ) :=
  D.atlas.family (((D.state_overlap (j+1)).angular).sub ((D.state_overlap j).angular))

/-- Pressure increment family, given by `D.atlas.family (((D.state_overlap (j+1)).pressure).sub
((D.state_overlap j).pressure))`. -/
noncomputable def pressureIncrementFamily (j : ℕ) :=
  D.atlas.family (((D.state_overlap (j+1)).pressure).sub ((D.state_overlap j).pressure))

theorem angularIncrement_native (j : ℕ) :
    (D.angularIncrementFamily j).native =
      ((p j).temporalIncrement (CycleState.iterate p c seed j).coefficients c
        (CycleState.iterate p c seed j).state).angular +
      ((p j).rankIncrement (CycleState.iterate p c seed j).coefficients c
        (CycleState.iterate p c seed j).state).angular := by
  change ((p j).next (CycleState.iterate p c seed j).coefficients c
    (CycleState.iterate p c seed j).state).mean.angular -
      (CycleState.iterate p c seed j).state.mean.angular = _
  rw [CycleParameters.next_mean]
  change (_ + _) + _ - _ = _
  abel

theorem pressureIncrement_native (j : ℕ) :
    (D.pressureIncrementFamily j).native = (CycleState.iterate p c seed (j+1)).state.pressure -
      (CycleState.iterate p c seed j).state.pressure := rfl

theorem angularIncrement_moving (j : ℕ) :
    GaugeMomentBalances.MovingField U G.inner G.outer (D.angularIncrementFamily j).native :=
  MeanStateRegularity.MovingField.sub (D.primitives (j+1)).mean.angular (D.primitives
      j).mean.angular

theorem pressureIncrement_moving
    (hseed : (VariableGaugeMean.reconstructState G.gauge c seed.state).pressure =
        seed.state.pressure)
    (j : ℕ) :
    GaugeMomentBalances.MovingField U G.inner G.outer (D.pressureIncrementFamily j).native :=
  MeanStateRegularity.MovingField.sub (D.pressure_moving hseed (j+1)) (D.pressure_moving hseed j)

theorem stream_moving (j : ℕ) :
    GaugeMomentBalances.MovingField U G.inner G.outer (D.streamFamily j).native :=
  MeanStateRegularity.MovingField.add (D.temporal_moving j) (D.rank_moving j)

end CycleData

/-! ## Native quantitative adapters for the actual run -/

section RunJets

variable {B N0 N : ℕ} {p : ℕ → CycleParameters (ActualInitialization.Index B N0)}
    (H : InitialCycleInput B N0 N p)

theorem cycleAngular_nativeJets (j : ℕ) (hN : 1 ≤ N)
    (HC : CorrectionState.CumulativeBounds ActualInitialMean.strip
      (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
          j).state) :
    PhysicalMeanJetBounds.NativeJets N standardRegion.carrier (h * (9 / 10))
      ((initialCycleData H).angularFamily j).native :=
  initial_nativeJets_of_class ((initialCycleData H).primitives j).mean.angular HC.velocity.angular
      N hN

theorem cyclePressure_nativeJets (j : ℕ) (hN : 1 ≤ N)
    (HC : CorrectionState.CumulativeBounds ActualInitialMean.strip
      (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
          j).state) :
    PhysicalMeanJetBounds.NativeJets N standardRegion.carrier (h * (9 / 10))
      ((initialCycleData H).pressureFamily j).native := by
  have hs : (VariableGaugeMean.reconstructState initialGeometry.gauge (commonContext B)
      (ActualInitialization.initialCycleState B N0).state).pressure =
      (ActualInitialization.initialCycleState B N0).state.pressure := by
    rw [initialGeometry_gauge]
    rfl
  exact initial_nativeJets_of_class ((initialCycleData H).pressure_moving hs j) HC.pressure N hN

theorem angularIncrement_nativeJets (j : ℕ) (hN : 1 ≤ N) {α : ℝ}
    (HT : MeanIncrementBounds.IncrementBounds ActualInitialMean.strip α
      ((p j).temporalIncrement
        (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
            j).coefficients
        (commonContext B) (CycleState.iterate p (commonContext B)
            (ActualInitialization.initialCycleState B N0) j).state))
    (HR : MeanIncrementBounds.IncrementBounds ActualInitialMean.strip α
      ((p j).rankIncrement
        (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
            j).coefficients
        (commonContext B) (CycleState.iterate p (commonContext B)
            (ActualInitialization.initialCycleState B N0) j).state)) :
    PhysicalMeanJetBounds.NativeJets N standardRegion.carrier (h * α)
      ((initialCycleData H).angularIncrementFamily j).native := by
  apply initial_nativeJets_of_class ((initialCycleData H).angularIncrement_moving j) _ N hN
  erw [CycleData.angularIncrement_native]
  exact HT.angular.add HR.angular

theorem pressureIncrement_nativeJets (j : ℕ) (hN : 1 ≤ N) {α : ℝ}
    (HC : WeightedClasses.MeanClass ActualInitialMean.strip α
      ((CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
          (j + 1)).state.pressure -
        (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
            j).state.pressure)) :
    PhysicalMeanJetBounds.NativeJets N standardRegion.carrier (h * α)
      ((initialCycleData H).pressureIncrementFamily j).native := by
  have hs : (VariableGaugeMean.reconstructState initialGeometry.gauge (commonContext B)
      (ActualInitialization.initialCycleState B N0).state).pressure =
      (ActualInitialization.initialCycleState B N0).state.pressure := by
    rw [initialGeometry_gauge]
    rfl
  exact initial_nativeJets_of_class ((initialCycleData H).pressureIncrement_moving hs j) HC N hN

end RunJets

/-! ## Actual Cartesian chart values and curls -/

theorem Atlas.field_on_chart {h d : ℝ} {N Δ : ℕ} (A : Atlas h N Δ)
    {U : Set Plane} {f : Scalar} (H : A.OverlapLaw U d f)
    {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) (n : ℕ) (hn : N ≤ n)
    {w : SpaceTime} (ht : w ∈ PhysicalWaveSum.preterminal)
    (hu : (PhysicalMeanJetBounds.graph h n (A.gap n) w).2.1 ∈ U)
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a j) :
    (A.family H).field w = ChartScales.Q n ^ (-d) * f n
      (ActualMeanPotentialRealization.chartPoint
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (A.index n))
        (PhysicalCurlCovariance.polarCoordinates a j w)) := by
  have hc := ActualMeanPotentialRealization.chartPoint_eq_graph ha j h n (A.gap n)
    (Nat.sub_le _ _) hw
  rw [A.index_eq hn] at hc
  rw [(A.family H).field_eq n hn ht hu]
  change ChartScales.Q n ^ (-d) * f n (PhysicalMeanJetBounds.graph h n (A.gap n) w) = _
  rw [hc]

theorem Atlas.stream_curl {h : ℝ} {N Δ : ℕ} (A : Atlas h N Δ)
    {U : Set Plane} (hU : IsOpen U) {f : Scalar}
    (H : A.OverlapLaw U (CoordinateAlgebra.A h - 1 / 2) f)
    (hf : ∀ n ≥ N, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U))
    {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) (n : ℕ) (hn : N ≤ n)
    {w : SpaceTime} (ht : w ∈ PhysicalWaveSum.preterminal)
    (hu : (PhysicalMeanJetBounds.graph h n (A.gap n) w).2.1 ∈ U)
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a j) :
    SpatialCurl.spatialCurl (A.family H).angularField w =
      let G := PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (A.index n)
      CyclePhysicalPrefixes.polarVelocityMap a j
        (CyclePhysicalPrefixes.velocityMap G (ActualMeanPotentialRealization.meridional G (f n))) w
            := by
  have hc := ActualMeanPotentialRealization.coherent_angularField_curl ha j (A.family H)
    hU n hn ht hu hw ((hf n hn).contDiffAt ((PhysicalMeanDomain.slowDomain_open hU).mem_nhds hu))
  change SpatialCurl.spatialCurl (A.family H).angularField w =
    CyclePhysicalPrefixes.polarVelocityMap a j (CyclePhysicalPrefixes.velocityMap
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (ChartScales.nativeIndex h n - A.gap
          n))
      (ActualMeanPotentialRealization.meridional
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (ChartScales.nativeIndex h n -
            A.gap n))
        (f n))) w at hc
  simpa only [A.index_eq hn] using hc

theorem Atlas.angular_field {h : ℝ} {N Δ : ℕ} (A : Atlas h N Δ)
    {U : Set Plane} {f : Scalar} (H : A.OverlapLaw U (CoordinateAlgebra.A h) f)
    {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) (n : ℕ) (hn : N ≤ n)
    {w : SpaceTime} (ht : w ∈ PhysicalWaveSum.preterminal)
    (hu : (PhysicalMeanJetBounds.graph h n (A.gap n) w).2.1 ∈ U)
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a j) :
    (A.family H).angularField w =
      let G := PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (A.index n)
      CyclePhysicalPrefixes.polarVelocityMap a j
        (CyclePhysicalPrefixes.velocityMap G (fun x => ![0, f n x.1, 0])) w := by
  let z := PhysicalCurlCovariance.polarCoordinates a j w
  have hz := ActualMeanPotentialRealization.polarCoordinates_valid ha j hw
  have hb := ActualMeanPotentialRealization.polarCoordinates_back ha j hw
  have hf := A.field_on_chart H ha j n hn ht hu hw
  change (A.family H).field w • PhysicalMeanJetBounds.angularVector
    (PhysicalGraphBounds.radialProjection w) = _
  rw [hf, ← hb, ActualMeanPotentialRealization.angularVector_forward hz.1,
    ActualMeanPotentialRealization.polar_forward ha j _ hz]
  simp only [CyclePhysicalPrefixes.velocityMap, LinearMap.coe_mk, AddHom.coe_mk,
    PhysicalResidualTZ.velocityTZ, PhysicalResidualBridge.ScaledGraph.velocity,
    PhysicalResidualBridge.commonGraph, ActualMeanPotentialRealization.chartPoint,
    PhysicalResidualTZ.graphMapTZ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, mul_zero, AxisymmetricResidual.pack, zero_smul, zero_add]
  simp [PhysicalCurlCovariance.polarCoordinates_forward ha j hz]

theorem Atlas.pressure_field {h : ℝ} {N Δ : ℕ} (A : Atlas h N Δ)
    {U : Set Plane} {f : Scalar} (H : A.OverlapLaw U (2 * CoordinateAlgebra.A h) f)
    {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) (n : ℕ) (hn : N ≤ n)
    {w : SpaceTime} (ht : w ∈ PhysicalWaveSum.preterminal)
    (hu : (PhysicalMeanJetBounds.graph h n (A.gap n) w).2.1 ∈ U)
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a j) :
    (A.family H).field w =
      let G := PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (A.index n)
      CyclePhysicalPrefixes.polarPressureMap a j
        (CyclePhysicalPrefixes.pressureMap G (fun x => f n x.1)) w := by
  rw [A.field_on_chart H ha j n hn ht hu hw]
  change ChartScales.Q n ^ (-(2 * CoordinateAlgebra.A h)) * _ =
    (ChartScales.Q n ^ (-CoordinateAlgebra.A h)) ^ 2 * _
  congr 1
  rw [pow_two, ← Real.rpow_add (ChartScales.Q_pos n)]
  congr 1
  ring

theorem Atlas.family_add_field {h d : ℝ} {N Δ : ℕ} (A : Atlas h N Δ)
    {U : Set Plane} {f g : Scalar} (Hf : A.OverlapLaw U d f) (Hg : A.OverlapLaw U d g) :
    (A.family (Hf.add Hg)).field = (A.family Hf).field + (A.family Hg).field := by
  funext w
  exact congrFun (A.physical_add U d f g) (PhysicalMeanJetBounds.physicalPoint h w)

theorem Atlas.family_add_angular {h d : ℝ} {N Δ : ℕ} (A : Atlas h N Δ)
    {U : Set Plane} {f g : Scalar} (Hf : A.OverlapLaw U d f) (Hg : A.OverlapLaw U d g) :
    (A.family (Hf.add Hg)).angularField = (A.family Hf).angularField + (A.family Hg).angularField
        := by
  funext w
  simp only [PhysicalMeanJetBounds.CoherentFamily.angularField, A.family_add_field Hf Hg,
    Pi.add_apply, add_smul]

theorem Atlas.family_sub_field {h d : ℝ} {N Δ : ℕ} (A : Atlas h N Δ)
    {U : Set Plane} {f g : Scalar} (Hf : A.OverlapLaw U d f) (Hg : A.OverlapLaw U d g) :
    (A.family (Hf.sub Hg)).field = (A.family Hf).field - (A.family Hg).field := by
  funext w
  exact congrFun (A.physical_sub U d f g) (PhysicalMeanJetBounds.physicalPoint h w)

theorem Atlas.family_sub_angular {h d : ℝ} {N Δ : ℕ} (A : Atlas h N Δ)
    {U : Set Plane} {f g : Scalar} (Hf : A.OverlapLaw U d f) (Hg : A.OverlapLaw U d g) :
    (A.family (Hf.sub Hg)).angularField = (A.family Hf).angularField - (A.family Hg).angularField
        := by
  funext w
  simp only [PhysicalMeanJetBounds.CoherentFamily.angularField, A.family_sub_field Hf Hg,
    Pi.sub_apply, sub_smul]

theorem initialStream_angularField (B N0 N : ℕ) :
    (initialStreamFamily B N0 N).angularField =
      (initialTemporalFamily B N0 N).angularField + (initialRankFamily B N0 N).angularField :=
  (initialAtlas N).family_add_angular (initialTemporal_overlap B N0 N) (initialRank_overlap B N0 N)

namespace CycleData

variable {ι : Type} {G : CycleStateCoherence.Geometry} {N Δ : ℕ}
    {p : ℕ → CycleParameters ι} {c : Context Point} {seed : CycleState ι}
    {U : LocalSignedRequest.SlowRegion (2 * G.h)} (D : CycleData G N Δ p c seed U)

theorem stream_angularField (j : ℕ) :
    (D.streamFamily j).angularField = (D.temporalFamily j).angularField + (D.rankFamily
        j).angularField :=
  D.atlas.family_add_angular (D.temporalScalar_overlap j) (D.rankScalar_overlap j)

theorem angularIncrement_angularField (j : ℕ) :
    (D.angularIncrementFamily j).angularField =
      (D.angularFamily (j+1)).angularField - (D.angularFamily j).angularField :=
  D.atlas.family_sub_angular (D.state_overlap (j+1)).angular (D.state_overlap j).angular

theorem pressureIncrement_field (j : ℕ) :
    (D.pressureIncrementFamily j).field = (D.pressureFamily (j+1)).field - (D.pressureFamily
        j).field :=
  D.atlas.family_sub_field (D.state_overlap (j+1)).pressure (D.state_overlap j).pressure

end CycleData

/-! ## Actual temporal-source and measured-debt class inputs -/

section SourceClasses

variable {B N0 N : ℕ} {p : ℕ → CycleParameters (ActualInitialization.Index B N0)}
    (H : InitialCycleInput B N0 N p)

theorem cycleTemporal_class (j : ℕ) {α : ℝ}
    (HC : WeightedClasses.MeanClass ActualInitialMean.strip α
      (((p j).afterSigned
        (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
            j).coefficients
        (commonContext B) (CycleState.iterate p (commonContext B)
            (ActualInitialization.initialCycleState B N0) j).state).axialResidual
        (commonContext B))) :
    WeightedClasses.MeanClass ActualInitialMean.strip α ((initialCycleData H).temporalFamily
        j).native := by
  let D := initialCycleData H
  have hg : (p j).gauge = commonGauge := (H.realizes j).gauge.trans initialGeometry_gauge
  have ht : (p j).timeExponent = h := (H.realizes j).timeExponent
  have hi : (p j).commonIndex = CorrectionInitialization.CommonWindow.index h := (H.realizes
      j).index
  have HP := (D.stage_primitives j).signed
  rw [hg] at HP
  have Hz := HP.axial_reconstructed (PrimaryTargetBounds.leftRadius_pos nominal)
    (ChartScales.radialExponent_pos h outgoing.data.h_pos.le) commonGauge_length
    (by rw [← hg]; rfl)
  have Hp := VariableGaugeMean.meanClass_temporalStreamPotential standardRegion
    (PrimaryTargetBounds.leftRadius_pos nominal) (PrimaryTargetBounds.radii_ordered nominal)
    (ChartScales.radialExponent_pos h outgoing.data.h_pos.le)
    (div_pos (FinalSlowBase.edgeExponent_pos nominal) (by norm_num)) zero_lt_one
    (ChartScales.epsilon h) BaseContextAssembly.slowScale (ChartScales.epsilon_pos h)
    (ChartScales.epsilon_le_one h outgoing.data.h_pos.le) BaseContextAssembly.one_le_slowScale
    outgoing.data.h_pos.le (fun n => le_max_right 1 (ChartScales.S n))
    (CorrectionInitialization.CommonWindow.index h) (CorrectionInitialization.CommonWindow.gap h)
    (CorrectionInitialization.CommonWindow.native_le_index_add h outgoing.data.h_pos.le)
    Hz.smooth Hz.periodic Hz.supported HC commonGauge.radial.frequency
    (fun _ => commonGauge.radial.radialDirection)
  change WeightedClasses.MeanClass ActualInitialMean.strip α
    (VariableGaugeMean.temporalPotential (p j).gauge (p j).timeExponent (p j).commonIndex _ _)
  rw [hg, ht, hi]
  exact Hp

theorem cycleRank_class (j : ℕ) {α : ℝ}
    (HC : WeightedClasses.UnweightedClass ActualInitialMean.slowStrip α
      (CorrectionState.debt (commonContext B)
        ((p j).afterTemporal
          (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
              j).coefficients
          (commonContext B) (CycleState.iterate p (commonContext B)
              (ActualInitialization.initialCycleState B N0) j).state))) :
    WeightedClasses.MeanClass ActualInitialMean.strip α ((initialCycleData H).rankFamily j).native
        := by
  have hg : (p j).gauge = commonGauge := (H.realizes j).gauge.trans initialGeometry_gauge
  have hr : (p j).rank = rankData := (H.realizes j).rank.trans initialGeometry_rank
  have HG := ((initialCycleData H).stage_primitives j).rankGeometry
  rw [hg, hr] at HG
  have Hp := rankPotential_class (cL := FinalSlowBase.edgeExponent nominal / 4) (cR := 1)
    standardRegion commonGauge rankData (commonContext B) _
    (PrimaryTargetBounds.leftRadius_pos nominal)
    (div_pos (FinalSlowBase.edgeExponent_pos nominal) (by norm_num)) zero_lt_one
    (ChartScales.epsilon h) BaseContextAssembly.slowScale (ChartScales.epsilon_pos h)
    (ChartScales.epsilon_le_one h outgoing.data.h_pos.le) BaseContextAssembly.one_le_slowScale
    HG (rankData_parameters standardRegion.carrier) rankAmplitude_pos.ne'
    active_left_before_rank rank_before_active_right HC
  change WeightedClasses.MeanClass ActualInitialMean.strip α (VariableGaugeMean.rankPotential (p
      j).gauge (p j).rank _ _)
  rw [hg, hr]
  exact Hp

theorem cycleTemporal_nativeJets (j : ℕ) (hN : 1 ≤ N) {α : ℝ}
    (HC : WeightedClasses.MeanClass ActualInitialMean.strip α
      (((p j).afterSigned
        (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
            j).coefficients
        (commonContext B) (CycleState.iterate p (commonContext B)
            (ActualInitialization.initialCycleState B N0) j).state).axialResidual
        (commonContext B))) :
    PhysicalMeanJetBounds.NativeJets N standardRegion.carrier (h * α)
      ((initialCycleData H).temporalFamily j).native :=
  initial_nativeJets_of_class ((initialCycleData H).temporal_moving j) (cycleTemporal_class H j HC)
      N hN

theorem cycleRank_nativeJets (j : ℕ) (hN : 1 ≤ N) {α : ℝ}
    (HC : WeightedClasses.UnweightedClass ActualInitialMean.slowStrip α
      (CorrectionState.debt (commonContext B)
        ((p j).afterTemporal
          (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
              j).coefficients
          (commonContext B) (CycleState.iterate p (commonContext B)
              (ActualInitialization.initialCycleState B N0) j).state))) :
    PhysicalMeanJetBounds.NativeJets N standardRegion.carrier (h * α)
      ((initialCycleData H).rankFamily j).native :=
  initial_nativeJets_of_class ((initialCycleData H).rank_moving j) (cycleRank_class H j HC) N hN

end SourceClasses

/-! ## The combined mean stream realizes the literal two mean increments -/

theorem Atlas.stream_add_curl {h : ℝ} {N Δ : ℕ} (A : Atlas h N Δ)
    {U : Set Plane} (hU : IsOpen U) {f g : Scalar}
    (Hf : A.OverlapLaw U (CoordinateAlgebra.A h - 1 / 2) f)
    (Hg : A.OverlapLaw U (CoordinateAlgebra.A h - 1 / 2) g)
    (hf : ∀ n ≥ N, ContDiffOn ℝ ∞ (f n) (PhysicalMeanDomain.slowDomain U))
    (hg : ∀ n ≥ N, ContDiffOn ℝ ∞ (g n) (PhysicalMeanDomain.slowDomain U))
    {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) (n : ℕ) (hn : N ≤ n)
    {w : SpaceTime} (ht : w ∈ PhysicalWaveSum.preterminal)
    (hu : (PhysicalMeanJetBounds.graph h n (A.gap n) w).2.1 ∈ U)
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a j) :
    SpatialCurl.spatialCurl (A.family (Hf.add Hg)).angularField w =
      let G := PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (A.index n)
      CyclePhysicalPrefixes.polarVelocityMap a j (CyclePhysicalPrefixes.velocityMap G
        (ActualMeanPotentialRealization.meridional G (f n) +
            ActualMeanPotentialRealization.meridional G (g n))) w := by
  have hfg := ActualMeanPotentialRealization.coherent_angularField_germ ha j (A.family Hf) hU n hn
      ht hu hw
  have hgg := ActualMeanPotentialRealization.coherent_angularField_germ ha j (A.family Hg) hU n hn
      ht hu hw
  change (A.family Hf).angularField =ᶠ[𝓝 w] ActualMeanPotentialRealization.cartesianPotential a j
    (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (ChartScales.nativeIndex h n - A.gap
        n)) (f n) at hfg
  change (A.family Hg).angularField =ᶠ[𝓝 w] ActualMeanPotentialRealization.cartesianPotential a j
    (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (ChartScales.nativeIndex h n - A.gap
        n)) (g n) at hgg
  rw [A.index_eq hn] at hfg hgg
  have hsum := hfg.add hgg
  change (A.family Hf).angularField + (A.family Hg).angularField =ᶠ[𝓝 w]
    ActualMeanPotentialRealization.cartesianPotential a j
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (A.index n)) (f n) +
      ActualMeanPotentialRealization.cartesianPotential a j
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h (A.index n)) (g n) at hsum
  rw [← A.family_add_angular Hf Hg] at hsum
  rw [PhysicalCurlCovariance.spatialCurl_congr hsum]
  apply ActualMeanPotentialRealization.cartesianPotential_add_curl ha j _
    (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _) _ _ hw
  · have hc := ActualMeanPotentialRealization.chartPoint_eq_graph ha j h n (A.gap n) (Nat.sub_le _
      _) hw
    rw [A.index_eq hn] at hc
    rw [hc]
    exact (hf n hn).contDiffAt ((PhysicalMeanDomain.slowDomain_open hU).mem_nhds hu)
  · have hc := ActualMeanPotentialRealization.chartPoint_eq_graph ha j h n (A.gap n) (Nat.sub_le _
      _) hw
    rw [A.index_eq hn] at hc
    rw [hc]
    exact (hg n hn).contDiffAt ((PhysicalMeanDomain.slowDomain_open hU).mem_nhds hu)

theorem initialGauge_matches (B n : ℕ) :
    ActualMeanPotentialRealization.GaugeMatches commonGauge (commonContext B)
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
          (CorrectionInitialization.CommonWindow.index h n)) n := by
  rw [ActualInitialCoherence.commonGauge_eq_similarity]
  exact ActualMeanPotentialRealization.similarityGauge_matches h _ _ _ _ (commonContext B) n rfl

theorem initialStream_curl (B N0 N n : ℕ) (hn : N ≤ n)
    {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) {w : SpaceTime}
    (ht : w ∈ PhysicalWaveSum.preterminal)
    (hu : (PhysicalMeanJetBounds.graph h n ((initialAtlas N).gap n) w).2.1 ∈ standardRegion.carrier)
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a j) :
    SpatialCurl.spatialCurl (initialStreamFamily B N0 N).angularField w =
      CyclePhysicalPrefixes.polarVelocityMap a j (CyclePhysicalPrefixes.velocityMap
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
            (CorrectionInitialization.CommonWindow.index h n))
        (CyclePhysicalPrefixes.meridionalComponents (ActualInitialCoherence.initialized B N0).mean
            n)) w := by
  unfold initialStreamFamily
  rw [(initialAtlas N).stream_add_curl standardRegion.isOpen
    (initialTemporal_overlap B N0 N) (initialRank_overlap B N0 N)
    (fun n _ => (initialTemporal_moving B N0).smooth n) (fun n _ => (initialRank_moving B
        N0).smooth n)
    ha j n hn ht hu hw]
  dsimp only [initialAtlas, commonAtlas, initialTemporalScalar, initialRankScalar]
  change CyclePhysicalPrefixes.polarVelocityMap a j (CyclePhysicalPrefixes.velocityMap
    (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
        (CorrectionInitialization.CommonWindow.index h n))
    (ActualMeanPotentialRealization.meridional
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
            (CorrectionInitialization.CommonWindow.index h n))
        (VariableGaugeMean.temporalPotential commonGauge h
            (CorrectionInitialization.CommonWindow.index h)
          (commonContext B) (ActualInitialCoherence.primary B N0) n) +
      ActualMeanPotentialRealization.meridional
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
            (CorrectionInitialization.CommonWindow.index h n))
        (VariableGaugeMean.rankPotential commonGauge rankData (commonContext B)
          (ActualInitialCoherence.temporal B N0) n))) w = _
  rw [ActualMeanPotentialRealization.meridional_temporal commonGauge h
    (CorrectionInitialization.CommonWindow.index h) (commonContext B)
        (ActualInitialCoherence.primary B N0)
    _ n (initialGauge_matches B n),
    ActualMeanPotentialRealization.meridional_rank commonGauge rankData (commonContext B)
      (ActualInitialCoherence.temporal B N0) _ n (initialGauge_matches B n)]
  rw [← ActualMeanPotentialRealization.meridionalComponents_updated]
  have hi := ActualMeanPotentialRealization.initializedBands_mean commonGauge rankData h
    (CorrectionInitialization.CommonWindow.index h) (commonContext B)
    (activeLabels standardRegion B N0) (ActualInitialCoherence.pieces B N0)
    (ActualInitialCoherence.baseError B)
  change (ActualInitialCoherence.initialized B N0).mean = _ at hi
  rw [hi]
  rfl

theorem cycleStream_curl {B N0 N : ℕ} {p : ℕ → CycleParameters (ActualInitialization.Index B N0)}
    (H : InitialCycleInput B N0 N p) (k n : ℕ) (hn : N ≤ n)
    {a : ℝ} (ha : 0 < a) (j : PolarCharts.Index) {w : SpaceTime}
    (ht : w ∈ PhysicalWaveSum.preterminal)
    (hu : (PhysicalMeanJetBounds.graph h n ((initialAtlas N).gap n) w).2.1 ∈ standardRegion.carrier)
    (hw : w ∈ ActualMeanPotentialRealization.cartesianDomain a j) :
    SpatialCurl.spatialCurl ((initialCycleData H).streamFamily k).angularField w =
      let x := CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
          k
      CyclePhysicalPrefixes.polarVelocityMap a j (CyclePhysicalPrefixes.velocityMap
        (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
            (CorrectionInitialization.CommonWindow.index h n))
        (CyclePhysicalPrefixes.meridionalComponents ((p k).temporalIncrement x.coefficients
            (commonContext B) x.state) n +
          CyclePhysicalPrefixes.meridionalComponents ((p k).rankIncrement x.coefficients
              (commonContext B) x.state) n)) w := by
  let D := initialCycleData H
  have hg : (p k).gauge = commonGauge := (H.realizes k).gauge.trans initialGeometry_gauge
  have hm : ActualMeanPotentialRealization.GaugeMatches (p k).gauge (commonContext B)
      (PhysicalResidualBridge.commonGraph (ChartScales.Q n) h
          (CorrectionInitialization.CommonWindow.index h n)) n := by
    rw [hg]
    exact initialGauge_matches B n
  have he := D.atlas.stream_add_curl standardRegion.isOpen (D.temporalScalar_overlap k)
      (D.rankScalar_overlap k)
    (fun n _ => (D.temporal_moving k).smooth n) (fun n _ => (D.rank_moving k).smooth n) ha j n hn
        ht hu hw
  dsimp only [CycleData.temporalScalar, CycleData.rankScalar, D, initialCycleData,
    initialAtlas, commonAtlas, initialGeometry] at he
  rw [ActualMeanPotentialRealization.meridional_temporal (p k).gauge (p k).timeExponent
    (p k).commonIndex (commonContext B) _ _ n hm,
    ActualMeanPotentialRealization.meridional_rank (p k).gauge (p k).rank (commonContext B) _ _ n
        hm] at he
  simp only [CycleParameters.temporalIncrement, CycleParameters.rankIncrement, (H.realizes
      k).axial] at he ⊢
  exact he

end NavierStokes.ActualMeanPhysicalData

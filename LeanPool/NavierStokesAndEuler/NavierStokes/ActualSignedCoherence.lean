/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualInitialization
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedStageControls
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPeriodizedSignedRealization

/-!
# Coherence of the literal signed correction

The current-state request is transported on entire radial and free-fast
fibers.  The signed quotient, its projected pressure, the native cutoff,
the periodized amplitude and the curl correction are then compared in
the actual charts.  No coherence of a signed output is assumed.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualSignedCoherence

open Set Function Filter HarmonicCalculus WeightedClasses
open CorrectionInitialization CorrectionInitialization.ActualPrimary GaugeStateCoherence
open scoped ContDiff Topology BigOperators InnerProductSpace

/-- Point: an abbreviation for `LocalSignedRequest.Point`. -/
abbrev Point := LocalSignedRequest.Point
/-- Full point: an abbreviation for `Point × ℝ`. -/
abbrev FullPoint := Point × ℝ
/-- Signed label: an abbreviation for `ActualSignedStageControls.SignedLabel B N0`. -/
abbrev SignedLabel (B N0 : ℕ) := ActualSignedStageControls.SignedLabel B N0

variable {B N0 : ℕ}

/-- Full strip, given by `HarmonicWaveInteraction.productStrip
ActualInitialization.geometry.strip`. -/
noncomputable def fullStrip : StripData FullPoint :=
  HarmonicWaveInteraction.productStrip ActualInitialization.geometry.strip

/-- Request, constructed using `LocalSignedRequest.fullRequest`. -/
noncomputable def request (B : ℕ) (u : CorrectionState.State Point) :
    ℕ → FullPoint → SignedWaveUpdate.Vec2 :=
  LocalSignedRequest.fullRequest ActualInitialization.geometry.strip
    ActualInitialization.geometry.patch ActualInitialization.geometry.coord (commonContext B) u

/-- Copies, given by `(ActualSignedStageControls.parameters l).copyData
ActualInitialization.geometry.strip (request B u)`. -/
noncomputable def copies (l : SignedLabel B N0) (u : CorrectionState.State Point) :
    PeriodizedWaveBounds.CopyData FullPoint TorusInverse.Frequency :=
  (ActualSignedStageControls.parameters l).copyData ActualInitialization.geometry.strip (request B
      u)

/-- Chart, bundling `toFun`, `invFun`, `left_inv`, `right_inv` and the required compatibility
proofs. -/
noncomputable def chart (n m k : ℕ) : FullPoint ≃L[ℝ] FullPoint where
  toFun x := (bandChartEquiv h n m k x.1, x.2)
  invFun x := ((bandChartEquiv h n m k).symm x.1, x.2)
  left_inv x := Prod.ext ((bandChartEquiv h n m k).symm_apply_apply x.1) rfl
  right_inv x := Prod.ext ((bandChartEquiv h n m k).apply_symm_apply x.1) rfl
  map_add' x y := Prod.ext (map_add (bandChartEquiv h n m k) x.1 y.1) rfl
  map_smul' a x := Prod.ext (map_smul (bandChartEquiv h n m k) a x.1) rfl
  continuous_toFun := ((bandChartEquiv h n m k).continuous.comp continuous_fst).prodMk
      continuous_snd
  continuous_invFun := ((bandChartEquiv h n m k).symm.continuous.comp continuous_fst).prodMk
      continuous_snd

@[simp] theorem chart_apply (n m k : ℕ) (x : FullPoint) :
    chart n m k x = (bandChartEquiv h n m k x.1, x.2) := rfl

/-- Coefficient weight, given by `PhysicalSignedWave.coefficientScale (ChartScales.epsilon h n)
(ChartScales.epsilon h m) (bandVelocityScale h n m)`. -/
noncomputable def coefficientWeight (n m : ℕ) : ℝ :=
  PhysicalSignedWave.coefficientScale (ChartScales.epsilon h n) (ChartScales.epsilon h m)
    (bandVelocityScale h n m)

/-- Phase weight, given by `(ChartScales.carrier h m : ℝ) / (ChartScales.carrier h n : ℝ)`. -/
noncomputable def phaseWeight (n m : ℕ) : ℝ :=
  (ChartScales.carrier h m : ℝ) / (ChartScales.carrier h n : ℝ)

/-- Clock weight, given by `PhysicalParticularWave.clockWeight h (ChartScales.Q n)
(ChartScales.Q m)`. -/
noncomputable def clockWeight (n m : ℕ) : ℝ :=
  PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q m)

theorem velocityWeight_eq (n m : ℕ) :
    PhysicalParticularWave.velocityWeight h (ChartScales.Q n) (ChartScales.Q m) =
      bandVelocityScale h n m :=
  PhysicalSignedWave.ratioPower_eq_div_rpow (ChartScales.Q_pos n) (ChartScales.Q_pos m) _

theorem radiusWeight_eq (n m : ℕ) :
    PhysicalParticularWave.ratioPower (ChartScales.Q n) (ChartScales.Q m) (1/2) =
      bandScale n m :=
  PhysicalSignedWave.ratioPower_eq_div_rpow (ChartScales.Q_pos n) (ChartScales.Q_pos m) _

theorem velocity_pos (n m : ℕ) : 0 < bandVelocityScale h n m :=
  Real.rpow_pos_of_pos (div_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m)) _

theorem coefficientWeight_pos (n m : ℕ) : 0 < coefficientWeight n m :=
  PhysicalSignedWave.coefficientScale_pos (ChartScales.epsilon_pos h n)
    (ChartScales.epsilon_pos h m) (velocity_pos n m)

theorem carrier_pos (n : ℕ) : 0 < (ChartScales.carrier h n : ℝ) := by
  exact Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h n)

theorem phaseWeight_ne (n m : ℕ) : phaseWeight n m ≠ 0 :=
  div_ne_zero (carrier_pos m).ne' (carrier_pos n).ne'

theorem carrier_phaseWeight (n m : ℕ) :
    (ChartScales.carrier h n : ℝ) * phaseWeight n m = ChartScales.carrier h m := by
  unfold phaseWeight
  exact mul_div_cancel₀ _ (carrier_pos n).ne'

theorem sqrt_scale (n m : ℕ) :
    Real.sqrt (ChartScales.Q n) = bandScale n m * Real.sqrt (ChartScales.Q m) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, mul_comm]
  exact (ActualPrimaryCoherence.band_power_cancel n m (1/2)).symm

theorem slowChange_eq (n m : ℕ) :
    PhysicalSignedWave.slowChange h (ChartScales.Q n) (ChartScales.Q m) =
      (bandSlowEquiv h n m).toContinuousLinearMap := by
  ext <;> simp [PhysicalSignedWave.slowChange, bandSlowEquiv_apply,
    PhysicalSignedWave.ratioPower_eq_div_rpow (ChartScales.Q_pos n) (ChartScales.Q_pos m)]

theorem requestChart_eq (n m k : ℕ) :
    PhysicalSignedWave.requestChart h (ChartScales.Q_pos n) (ChartScales.Q_pos m) k =
      bandChartEquiv h n m k := by
  apply ContinuousLinearEquiv.toLinearEquiv_injective
  apply LinearEquiv.ext
  intro x
  change PhysicalSignedWave.requestChart h (ChartScales.Q_pos n) (ChartScales.Q_pos m) k x =
    bandChartEquiv h n m k x
  simp only [PhysicalSignedWave.requestChart_apply, bandChartEquiv_apply,
    radiusWeight_eq, slowChange_eq, ContinuousLinearEquiv.coe_coe]

theorem chart_absolute (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m) (x : FullPoint) :
    ActualPrimaryCoherence.absoluteChart m (chart n m k x) =
      ActualPrimaryCoherence.absoluteChart n x := by
  exact Prod.ext (ActualPrimaryCoherence.toAbsolute_bandChart n m k hi x.1) rfl

theorem nativePoint_transport (l : SignedLabel B N0) (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (copy : TorusInverse.Frequency) (x : FullPoint) :
    ActualSignedStageControls.nativePoint l n copy x =
      ActualSignedStageControls.nativePoint l m copy (chart n m k x) := by
  simp only [ActualSignedStageControls.nativePoint, chart_apply,
    ActualPrimaryCoherence.toAbsolute_bandChart n m k hi]

theorem chart_radius (n m k : ℕ) (x : FullPoint) :
    (chart n m k x).1.1 = bandScale n m * x.1.1 := rfl

theorem chart_radial (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m) (x : FullPoint) :
    chart n m k ((ActualSignedStageControls.directions B).radialField n x) =
      bandScale n m • (ActualSignedStageControls.directions B).radialField m (chart n m k x) := by
  apply (ActualPrimaryCoherence.absoluteChart m).injective
  rw [chart_absolute n m k hi, map_smul]
  change ActualPrimaryCoherence.absoluteChart n
      ((PrimaryResidualClass.directions (commonContext B)).radialField n x) =
    bandScale n m • ActualPrimaryCoherence.absoluteChart m
      ((PrimaryResidualClass.directions (commonContext B)).radialField m (chart n m k x))
  rw [ActualPrimaryCoherence.absoluteChart_radial, ActualPrimaryCoherence.absoluteChart_radial,
    chart_absolute n m k hi, smul_smul, ← sqrt_scale]

theorem chart_angular (n m k : ℕ)
    (_hi : CommonWindow.index h n + k = CommonWindow.index h m) (_x : FullPoint) :
    chart n m k (ActualSignedStageControls.directions B).angular =
      (ActualSignedStageControls.directions B).angular := by
  change (bandChartEquiv h n m k (0 : Point), (1 : ℝ)) = (0, 1)
  rw [map_zero]

theorem chart_axial (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m) (x : FullPoint) :
    chart n m k ((ActualSignedStageControls.directions B).axialField fullStrip n x) =
      bandScale n m • (ActualSignedStageControls.directions B).axialField fullStrip m (chart n m k
          x) := by
  apply (ActualPrimaryCoherence.absoluteChart m).injective
  rw [chart_absolute n m k hi, map_smul]
  change ActualPrimaryCoherence.absoluteChart n
      ((PrimaryResidualClass.directions (commonContext B)).axialField
        (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal
            standardRegion)) n x) =
    bandScale n m • ActualPrimaryCoherence.absoluteChart m
      ((PrimaryResidualClass.directions (commonContext B)).axialField
        (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip nominal
            standardRegion)) m (chart n m k x))
  rw [ActualPrimaryCoherence.absoluteChart_axial, ActualPrimaryCoherence.absoluteChart_axial,
    chart_absolute n m k hi, smul_smul, ← sqrt_scale]

theorem clockWeight_eq (n m : ℕ) :
    clockWeight n m = bandVelocityScale h n m * bandScale n m := by
  rw [← velocityWeight_eq, ← radiusWeight_eq]
  exact (PhysicalParticularWave.ratioPower_mul (ChartScales.Q_pos n) (ChartScales.Q_pos m)
    (CoordinateAlgebra.A h) (1/2)).symm

theorem clockWeight_fast (n m : ℕ) :
    ChartScales.Q n ^ (1+h) = clockWeight n m * ChartScales.Q m ^ (1+h) := by
  change _ = (ChartScales.Q n ^ (CoordinateAlgebra.A h + 1/2) /
    ChartScales.Q m ^ (CoordinateAlgebra.A h + 1/2)) * _
  rw [show CoordinateAlgebra.A h + 1/2 = 1+h by unfold CoordinateAlgebra.A; ring]
  exact (div_mul_cancel₀ _ (Real.rpow_pos_of_pos (ChartScales.Q_pos m) (1+h)).ne').symm

theorem chart_fast (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m) (x : FullPoint) :
    chart n m k ((ActualSignedStageControls.directions B).fastField n x) =
      clockWeight n m • (ActualSignedStageControls.directions B).fastField m (chart n m k x) := by
  apply (ActualPrimaryCoherence.absoluteChart m).injective
  rw [chart_absolute n m k hi, map_smul]
  change ActualPrimaryCoherence.absoluteChart n
      ((PrimaryResidualClass.directions (commonContext B)).fastField n x) =
    clockWeight n m • ActualPrimaryCoherence.absoluteChart m
      ((PrimaryResidualClass.directions (commonContext B)).fastField m (chart n m k x))
  rw [ActualPrimaryCoherence.absoluteChart_fast, ActualPrimaryCoherence.absoluteChart_fast,
    chart_absolute n m k hi, smul_smul, ← clockWeight_fast]

theorem ratioPower_comp (n m r : ℕ) (a : ℝ) :
    PhysicalParticularWave.ratioPower (ChartScales.Q n) (ChartScales.Q r) a =
      PhysicalParticularWave.ratioPower (ChartScales.Q n) (ChartScales.Q m) a *
      PhysicalParticularWave.ratioPower (ChartScales.Q m) (ChartScales.Q r) a := by
  unfold PhysicalParticularWave.ratioPower
  field_simp [(Real.rpow_pos_of_pos (ChartScales.Q_pos m) a).ne']

private theorem coefficient_scale_algebra (a b c e f : ℝ) (he : e ≠ 0) (hf : f ≠ 0) :
    (a*b)*c/e = (a*f/e)*(b*c/f) := by
  field_simp

private theorem normal_scale_algebra (K Km Kr a b : ℝ) (hK : K ≠ 0) (hKm : Km ≠ 0) :
    (Kr/K)*(a*b) = ((Km/K)*a)*((Kr/Km)*b) := by
  field_simp

theorem coefficientScale_comp (l : SignedLabel B N0) (n m : ℕ) :
    ActualSignedStageControls.coefficientScale l n =
      coefficientWeight n m * ActualSignedStageControls.coefficientScale l m := by
  unfold ActualSignedStageControls.coefficientScale coefficientWeight
      PhysicalSignedWave.coefficientScale
  rw [← velocityWeight_eq]
  change (PhysicalParticularWave.ratioPower (ChartScales.Q n) (ChartScales.Q
      (BaseChartJets.cellBand l.1))
      (CoordinateAlgebra.A h) * _ / _) = _
  rw [ratioPower_comp n m (BaseChartJets.cellBand l.1)]
  unfold PhysicalParticularWave.velocityWeight
  exact coefficient_scale_algebra _ _ _ _ _
    (Real.sqrt_pos.mpr (ChartScales.epsilon_pos h n)).ne'
    (Real.sqrt_pos.mpr (ChartScales.epsilon_pos h m)).ne'

theorem normalScale_comp (l : SignedLabel B N0) (n m : ℕ) :
    ActualSignedStageControls.normalScale l n =
      (phaseWeight n m * bandScale n m) * ActualSignedStageControls.normalScale l m := by
  unfold ActualSignedStageControls.normalScale PhysicalParticularWave.normalWeight phaseWeight
  rw [← radiusWeight_eq, ratioPower_comp n m (BaseChartJets.cellBand l.1)]
  exact normal_scale_algebra _ _ _ _ _ (carrier_pos n).ne' (carrier_pos m).ne'

theorem clockScale_comp (l : SignedLabel B N0) (n m : ℕ) :
    ActualSignedStageControls.clockScale l n =
      clockWeight n m * ActualSignedStageControls.clockScale l m :=
  ratioPower_comp n m (BaseChartJets.cellBand l.1) (CoordinateAlgebra.A h + 1/2)

theorem target_transport (l : SignedLabel B N0) (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (copy : TorusInverse.Frequency) (x : FullPoint) :
    ActualSignedStageControls.target l copy n x = coefficientWeight n m ^ 2 •
      ActualSignedStageControls.target l copy m (chart n m k x) := by
  unfold ActualSignedStageControls.target
  rw [nativePoint_transport l n m k hi, coefficientScale_comp l n m, mul_pow, smul_smul]

theorem cutoff_transport (l : SignedLabel B N0) (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (copy : TorusInverse.Frequency) (x : FullPoint) :
    ActualSignedStageControls.cutoff l copy n x =
      ActualSignedStageControls.cutoff l copy m (chart n m k x) := by
  unfold ActualSignedStageControls.cutoff
  rw [nativePoint_transport l n m k hi]

theorem phase_transport (l : SignedLabel B N0) (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m) :
    (chartCoefficients l.2 l.1).phase n = fun x =>
      phaseWeight n m * (chartCoefficients l.2 l.1).phase m (chart n m k x) := by
  funext x
  rw [ActualPrimaryCoherence.phase_representation, ActualPrimaryCoherence.phase_representation]
  simp only [chart_absolute n m k hi, phaseWeight]
  field_simp [(carrier_pos n).ne', (carrier_pos m).ne']

theorem carrier_transport (l : SignedLabel B N0) (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m) (x : FullPoint) :
    (chartCoefficients l.2 l.1).frequency n * (chartCoefficients l.2 l.1).phase n x =
      (chartCoefficients l.2 l.1).frequency m * (chartCoefficients l.2 l.1).phase m (chart n m k x)
          := by
  rw [chartCoefficients_phase, chartCoefficients_phase]
  exact congrArg (absolutePhase l.2 l.1) (chart_absolute n m k hi x).symm

theorem normal_transport (l : SignedLabel B N0) (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m) (x : FullPoint) :
    (chartCoefficients l.2 l.1).normal fullStrip (ActualSignedStageControls.directions B) n x =
      (phaseWeight n m * bandScale n m) •
        (chartCoefficients l.2 l.1).normal fullStrip (ActualSignedStageControls.directions B) m
            (chart n m k x) := by
  unfold LinearWaveBounds.WaveCoefficients.normal
  rw [phase_transport l n m k hi]
  exact ActualPrimaryCoherence.phaseNormal_equiv (chart n m k) (bandScale_pos n m).ne'
    (fun x => x.1.1) (fun x => x.1.1) _ _ _ _ _ _ (chart_radius n m k)
    (chart_radial n m k hi) (chart_angular n m k hi) (chart_axial n m k hi) _ _ x

theorem normalMotion_transport (l : SignedLabel B N0) (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (copy : TorusInverse.Frequency) (x : FullPoint) :
    ActualSignedStageControls.normalMotion l copy n x =
      ((phaseWeight n m * bandScale n m) * clockWeight n m) •
        ActualSignedStageControls.normalMotion l copy m (chart n m k x) := by
  unfold ActualSignedStageControls.normalMotion
  rw [normalScale_comp l n m, clockScale_comp l n m, nativePoint_transport l n m k hi, smul_smul]
  congr 1
  ring

theorem action_transport (l : SignedLabel B N0) (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (copy : TorusInverse.Frequency) (x : FullPoint) :
    ActualSignedStageControls.action l copy n x =
      clockWeight n m • ActualSignedStageControls.action l copy m (chart n m k x) := by
  unfold ActualSignedStageControls.action
  rw [clockScale_comp l n m, nativePoint_transport l n m k hi, smul_smul]

/-! ## The request follows from the incoming state on all integration fibers. -/

theorem fullRequest_transport (u : CorrectionState.State Point)
    (H : MeanStateRegularity.PrimitiveData ActualInitialization.geometry.region
      ActualInitialization.geometry.patch.a ActualInitialization.geometry.patch.b (commonContext B)
          u)
    (hfixed : (VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
      (commonContext B) u).pressure = u.pressure)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (HS : PhysicalResidualNaturality.StateOn (PhysicalMeanDomain.slowDomain
        (ActualInitialCoherence.overlap n m))
      (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m) u u n m)
    (x : FullPoint) (hx : x.1.2.1 ∈ ActualInitialCoherence.overlap n m) :
    request B u n x = coefficientWeight n m ^ 2 • request B u m (chart n m k x) := by
  have H' : MeanStateRegularity.PrimitiveData ActualInitialization.geometry.region
      ActualInitialization.geometry.gauge.radial.inner
          ActualInitialization.geometry.gauge.radial.outer
      (commonContext B) u := by
    simpa only [ActualInitialization.geometry.inner_eq, ActualInitialization.geometry.outer_eq]
        using H
  have htheta := H.theta ActualInitialization.geometry.patch.a_pos
      ActualInitialization.geometry.patch.a_lt_b
  have hz := H'.axial_reconstructed ActualInitialization.geometry.inner_pos
    ActualInitialization.geometry.exponent_pos ActualInitialization.geometry.length_eq hfixed
  have ht : 0 < x.1.2.1.1 := standardRegion.time_pos x.1.2.1 hx.1
  have HC := ActualInitialCoherence.context_band B
    (V := ActualInitialCoherence.overlap n m) (fun t ht => standardRegion.time_pos t ht.1) n m k hi
  have he := PhysicalSignedWave.fullRequest_of_state
    ActualInitialization.geometry.strip ActualInitialization.geometry.strip
        ActualInitialization.geometry.patch
    outgoing.data.h_pos outgoing.data.h_lt_half (ChartScales.Q_pos n) (ChartScales.Q_pos m)
    (commonContext B) (commonContext B) u u n m k
    ((ActualInitialCoherence.overlap_open n m).preimage (continuous_fst.comp continuous_snd))
    (by simp only [requestChart_eq, velocityWeight_eq, radiusWeight_eq]; exact HS)
    (by simp only [requestChart_eq, velocityWeight_eq, radiusWeight_eq]; exact HC)
    x.1.2.1 ht (fun _ _ => hx) standardRegion.isOpen
    (by simp only [slowChange_eq, ContinuousLinearEquiv.coe_coe]; exact hx.2)
    (htheta.smooth m) (hz.smooth m) (htheta.periodic m) (hz.periodic m) x.1.1 x.1.2.2 x.2
  simp only [velocityWeight_eq, requestChart_eq] at he
  exact he

/-! ## The literal signed quotient and homogeneous pressure -/

theorem signedVector_of_request (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (copy : TorusInverse.Frequency) (x : FullPoint)
    (hR : request B u n x = coefficientWeight n m ^ 2 • request B u m (chart n m k x)) :
    SignedWaveUpdate.signedVector fullStrip (ActualSignedStageControls.matrix l copy)
      (ActualSignedStageControls.target l copy) (request B u) (ActualSignedStageControls.mask l
          copy)
      (ActualSignedStageControls.fundamental l copy) l.2 n x =
    bandVelocityScale h n m •
      SignedWaveUpdate.signedVector fullStrip (ActualSignedStageControls.matrix l copy)
        (ActualSignedStageControls.target l copy) (request B u) (ActualSignedStageControls.mask l
            copy)
        (ActualSignedStageControls.fundamental l copy) l.2 m (chart n m k x) := by
  apply PhysicalSignedWave.signedVector_transport fullStrip fullStrip
    (ActualSignedStageControls.matrix l copy) (ActualSignedStageControls.matrix l copy)
    (ActualSignedStageControls.target l copy) (request B u)
    (ActualSignedStageControls.target l copy) (request B u)
    (ActualSignedStageControls.mask l copy) (ActualSignedStageControls.mask l copy)
    (ActualSignedStageControls.fundamental l copy) (ActualSignedStageControls.fundamental l copy)
    n m x (chart n m k x) (velocity_pos n m)
  · simp only [ActualSignedStageControls.matrix, nativePoint_transport l n m k hi]
  · exact target_transport l n m k hi copy x
  · exact hR
  · simp only [ActualSignedStageControls.mask, nativePoint_transport l n m k hi]
  · simp only [ActualSignedStageControls.fundamental, nativePoint_transport l n m k hi]

theorem raw_amplitude_of_request (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (copy : TorusInverse.Frequency) (x : FullPoint)
    (hR : request B u n x = coefficientWeight n m ^ 2 • request B u m (chart n m k x)) :
    (copies l u).amplitude n copy x =
      bandVelocityScale h n m • (copies l u).amplitude m copy (chart n m k x) := by
  change CurlClassBounds.complexify
      (SignedWaveUpdate.signedVector fullStrip (ActualSignedStageControls.matrix l copy)
        (ActualSignedStageControls.target l copy) (request B u) (ActualSignedStageControls.mask l
            copy)
        (ActualSignedStageControls.fundamental l copy) l.2 n x) =
    bandVelocityScale h n m • CurlClassBounds.complexify
      (SignedWaveUpdate.signedVector fullStrip (ActualSignedStageControls.matrix l copy)
        (ActualSignedStageControls.target l copy) (request B u) (ActualSignedStageControls.mask l
            copy)
        (ActualSignedStageControls.fundamental l copy) l.2 m (chart n m k x))
  rw [signedVector_of_request l u n m k hi copy x hR, map_smul]

theorem raw_amplitude_transport (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (H : MeanStateRegularity.PrimitiveData ActualInitialization.geometry.region
      ActualInitialization.geometry.patch.a ActualInitialization.geometry.patch.b (commonContext B)
          u)
    (hfixed : (VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
      (commonContext B) u).pressure = u.pressure)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (HS : PhysicalResidualNaturality.StateOn (PhysicalMeanDomain.slowDomain
        (ActualInitialCoherence.overlap n m))
      (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m) u u n m)
    (copy : TorusInverse.Frequency) (x : FullPoint) (hx : x.1.2.1 ∈ ActualInitialCoherence.overlap
        n m) :
    (copies l u).amplitude n copy x =
      bandVelocityScale h n m • (copies l u).amplitude m copy (chart n m k x) :=
  raw_amplitude_of_request l u n m k hi copy x (fullRequest_transport u H hfixed n m k hi HS x hx)

theorem pressure_factor (n m : ℕ) :
    (clockWeight n m * bandVelocityScale h n m / (phaseWeight n m * bandScale n m)) *
      phaseWeight n m = bandVelocityScale h n m * bandVelocityScale h n m := by
  rw [clockWeight_eq]
  field_simp [phaseWeight_ne n m, (bandScale_pos n m).ne']

theorem raw_pressure_of_request (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (copy : TorusInverse.Frequency) (x : FullPoint)
    (hR : request B u n x = coefficientWeight n m ^ 2 • request B u m (chart n m k x)) :
    (copies l u).pressure n copy x =
      (bandVelocityScale h n m * bandVelocityScale h n m) •
        (copies l u).pressure m copy (chart n m k x) := by
  let v := SignedWaveUpdate.signedVector fullStrip (ActualSignedStageControls.matrix l copy)
    (ActualSignedStageControls.target l copy) (request B u) (ActualSignedStageControls.mask l copy)
    (ActualSignedStageControls.fundamental l copy) l.2
  have hv : v n x = bandVelocityScale h n m • v m (chart n m k x) :=
    signedVector_of_request l u n m k hi copy x hR
  change ActualPeriodizedSignedRealization.homogeneousPressure (ChartScales.carrier h n)
    ((chartCoefficients l.2 l.1).normal fullStrip (ActualSignedStageControls.directions B) n x)
    (ActualSignedStageControls.normalMotion l copy n x)
    (ActualSignedStageControls.action l copy n x) (v n x) =
    (bandVelocityScale h n m * bandVelocityScale h n m) •
      ActualPeriodizedSignedRealization.homogeneousPressure (ChartScales.carrier h m)
        ((chartCoefficients l.2 l.1).normal fullStrip (ActualSignedStageControls.directions B) m
            (chart n m k x))
        (ActualSignedStageControls.normalMotion l copy m (chart n m k x))
        (ActualSignedStageControls.action l copy m (chart n m k x)) (v m (chart n m k x))
  unfold ActualPeriodizedSignedRealization.homogeneousPressure
  rw [normal_transport l n m k hi, normalMotion_transport l n m k hi,
    action_transport l n m k hi, hv]
  simp only [_root_.smul_apply, map_smul, smul_smul]
  have hf : (clockWeight n m * bandVelocityScale h n m / (phaseWeight n m * bandScale n m)) *
      ((ChartScales.carrier h m : ℝ) / (ChartScales.carrier h n : ℝ)) =
      bandVelocityScale h n m * bandVelocityScale h n m := pressure_factor n m
  have hp := PhysicalSignedWave.homogeneousPressure_scale (ChartScales.carrier h n)
      (ChartScales.carrier h m)
      (clockWeight n m) (bandVelocityScale h n m) (phaseWeight n m * bandScale n m)
      (carrier_pos n).ne' (carrier_pos m).ne' (mul_ne_zero (phaseWeight_ne n m) (bandScale_pos n
          m).ne')
      ((chartCoefficients l.2 l.1).normal fullStrip (ActualSignedStageControls.directions B) m
          (chart n m k x))
      (ActualSignedStageControls.normalMotion l copy m (chart n m k x))
      (v m (chart n m k x))
      (ActualSignedStageControls.action l copy m (chart n m k x) (v m (chart n m k x)))
  rw [hf] at hp
  simpa only [mul_comm (clockWeight n m) (bandVelocityScale h n m)] using hp

theorem common_amplitude_of_request (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (x : FullPoint)
    (hR : request B u n x = coefficientWeight n m ^ 2 • request B u m (chart n m k x)) :
    (copies l u).common.amplitude n x =
      bandVelocityScale h n m • (copies l u).common.amplitude m (chart n m k x) := by
  change (∑' copy, ActualSignedStageControls.cutoff l copy n x • (copies l u).amplitude n copy x) =
    bandVelocityScale h n m •
      ∑' copy, ActualSignedStageControls.cutoff l copy m (chart n m k x) •
        (copies l u).amplitude m copy (chart n m k x)
  calc
    _ = ∑' copy, bandVelocityScale h n m •
        (ActualSignedStageControls.cutoff l copy m (chart n m k x) •
          (copies l u).amplitude m copy (chart n m k x)) := by
      apply tsum_congr
      intro copy
      rw [cutoff_transport l n m k hi, raw_amplitude_of_request l u n m k hi copy x hR]
      exact smul_comm _ _ _
    _ = _ := tsum_const_smul'' _

theorem common_pressure_of_request (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (x : FullPoint)
    (hR : request B u n x = coefficientWeight n m ^ 2 • request B u m (chart n m k x)) :
    (copies l u).common.pressure n x =
      (bandVelocityScale h n m * bandVelocityScale h n m) •
        (copies l u).common.pressure m (chart n m k x) := by
  change (∑' copy, ActualSignedStageControls.cutoff l copy n x • (copies l u).pressure n copy x) =
    (bandVelocityScale h n m * bandVelocityScale h n m) •
      ∑' copy, ActualSignedStageControls.cutoff l copy m (chart n m k x) •
        (copies l u).pressure m copy (chart n m k x)
  calc
    _ = ∑' copy, (bandVelocityScale h n m * bandVelocityScale h n m) •
        (ActualSignedStageControls.cutoff l copy m (chart n m k x) •
          (copies l u).pressure m copy (chart n m k x)) := by
      apply tsum_congr
      intro copy
      rw [cutoff_transport l n m k hi, raw_pressure_of_request l u n m k hi copy x hR]
      exact smul_comm _ _ _
    _ = _ := tsum_const_smul'' _

theorem common_amplitude_germ (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (H : MeanStateRegularity.PrimitiveData ActualInitialization.geometry.region
      ActualInitialization.geometry.patch.a ActualInitialization.geometry.patch.b (commonContext B)
          u)
    (hfixed : (VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
      (commonContext B) u).pressure = u.pressure)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (HS : PhysicalResidualNaturality.StateOn (PhysicalMeanDomain.slowDomain
        (ActualInitialCoherence.overlap n m))
      (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m) u u n m)
    (x : FullPoint) (hx : x.1.2.1 ∈ ActualInitialCoherence.overlap n m) :
    (copies l u).common.amplitude n =ᶠ[𝓝 x]
      fun y => bandVelocityScale h n m • (copies l u).common.amplitude m (chart n m k y) := by
  have hU : {y : FullPoint | y.1.2.1 ∈ ActualInitialCoherence.overlap n m} ∈ 𝓝 x :=
    ((ActualInitialCoherence.overlap_open n m).preimage continuous_fst.snd.fst).mem_nhds hx
  filter_upwards [hU] with y hy
  exact common_amplitude_of_request l u n m k hi y (fullRequest_transport u H hfixed n m k hi HS y
      hy)

theorem corrected_amplitude_transport (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (H : MeanStateRegularity.PrimitiveData ActualInitialization.geometry.region
      ActualInitialization.geometry.patch.a ActualInitialization.geometry.patch.b (commonContext B)
          u)
    (hfixed : (VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
      (commonContext B) u).pressure = u.pressure)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (HS : PhysicalResidualNaturality.StateOn (PhysicalMeanDomain.slowDomain
        (ActualInitialCoherence.overlap n m))
      (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m) u u n m)
    (x : FullPoint) (hx : x.1.2.1 ∈ ActualInitialCoherence.overlap n m) :
    ((copies l u).commonCorrected fullStrip (ActualSignedStageControls.directions B)).amplitude n x
        =
      bandVelocityScale h n m •
        ((copies l u).commonCorrected fullStrip (ActualSignedStageControls.directions B)).amplitude
            m
          (chart n m k x) := by
  change CurlClassBounds.realizedCoefficient (ChartScales.carrier h n) (fun y : FullPoint => y.1.1)
      ((ActualSignedStageControls.directions B).radialField n)
      (fun _ => (ActualSignedStageControls.directions B).angular)
      ((ActualSignedStageControls.directions B).axialField fullStrip n)
      ((chartCoefficients l.2 l.1).phase n) ((copies l u).common.amplitude n) x =
    bandVelocityScale h n m •
      CurlClassBounds.realizedCoefficient (ChartScales.carrier h m) (fun y : FullPoint => y.1.1)
        ((ActualSignedStageControls.directions B).radialField m)
        (fun _ => (ActualSignedStageControls.directions B).angular)
        ((ActualSignedStageControls.directions B).axialField fullStrip m)
        ((chartCoefficients l.2 l.1).phase m) ((copies l u).common.amplitude m) (chart n m k x)
  have ha := common_amplitude_germ l u H hfixed n m k hi HS x hx
  have he := (ParticularWaveAssembly.realizedCoefficient_germ ha
    (ChartScales.carrier h n) (fun y : FullPoint => y.1.1)
    ((ActualSignedStageControls.directions B).radialField n)
    (fun _ => (ActualSignedStageControls.directions B).angular)
    ((ActualSignedStageControls.directions B).axialField fullStrip n)
    ((chartCoefficients l.2 l.1).phase n)).self_of_nhds
  rw [he, phase_transport l n m k hi]
  exact ActualPrimaryCoherence.realizedCoefficient_equiv (chart n m k)
    (bandScale_pos n m).ne' (phaseWeight_ne n m) (carrier_pos n).ne' (carrier_phaseWeight n m)
    (fun y => y.1.1) (fun y => y.1.1) _ _ _ _ _ _ (chart_radius n m k)
    (chart_radial n m k hi) (chart_angular n m k hi) (chart_axial n m k hi)
    (bandVelocityScale h n m) ((chartCoefficients l.2 l.1).phase m) ((copies l u).common.amplitude
        m) x

theorem exactBlock_velocity_transport (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (H : MeanStateRegularity.PrimitiveData ActualInitialization.geometry.region
      ActualInitialization.geometry.patch.a ActualInitialization.geometry.patch.b (commonContext B)
          u)
    (hfixed : (VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
      (commonContext B) u).pressure = u.pressure)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (HS : PhysicalResidualNaturality.StateOn (PhysicalMeanDomain.slowDomain
        (ActualInitialCoherence.overlap n m))
      (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m) u u n m)
    (x : Point) (hx : x.2.1 ∈ ActualInitialCoherence.overlap n m) (theta : ℝ) (i : Fin 3) :
    ((ActualSignedStageControls.parameters l).exactBlock ActualInitialization.geometry.strip
      (request B u)).oscillation n (x,theta) i =
    bandVelocityScale h n m *
      ((ActualSignedStageControls.parameters l).exactBlock ActualInitialization.geometry.strip
        (request B u)).oscillation m (bandChartEquiv h n m k x,theta) i := by
  let C := (copies l u).commonCorrected fullStrip (ActualSignedStageControls.directions B)
  let a := (ActualSignedStageControls.parameters l).angularFrequency
  have ha : C.amplitude n (x,0) =
      bandVelocityScale h n m • C.amplitude m (bandChartEquiv h n m k x,0) :=
    corrected_amplitude_transport l u H hfixed n m k hi HS (x,0) hx
  have hmode : a n = a m := rfl
  have hphase := carrier_transport l n m k hi (x,0)
  change (SignedWaveUpdate.blockOfCoefficients C a).oscillation n (x,theta) i =
    bandVelocityScale h n m *
      (SignedWaveUpdate.blockOfCoefficients C a).oscillation m (bandChartEquiv h n m k x,theta) i
  simp only [SignedWaveUpdate.blockOfCoefficients, SignedWaveUpdate.coefficientBlock_velocity]
  change (C.amplitude n (x,0) i * HarmonicFields.character 1
      ((chartCoefficients l.2 l.1).frequency n * (chartCoefficients l.2 l.1).phase n (x,0) +
        (a n : ℝ) * theta)).re =
    bandVelocityScale h n m * (C.amplitude m (bandChartEquiv h n m k x,0) i *
      HarmonicFields.character 1 ((chartCoefficients l.2 l.1).frequency m *
        (chartCoefficients l.2 l.1).phase m (chart n m k (x,0)) + (a m : ℝ) * theta)).re
  rw [ha, hphase, hmode]
  simp only [Pi.smul_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem exactBlock_pressure_transport (l : SignedLabel B N0) (u : CorrectionState.State Point)
    (H : MeanStateRegularity.PrimitiveData ActualInitialization.geometry.region
      ActualInitialization.geometry.patch.a ActualInitialization.geometry.patch.b (commonContext B)
          u)
    (hfixed : (VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
      (commonContext B) u).pressure = u.pressure)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (HS : PhysicalResidualNaturality.StateOn (PhysicalMeanDomain.slowDomain
        (ActualInitialCoherence.overlap n m))
      (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m) u u n m)
    (x : Point) (hx : x.2.1 ∈ ActualInitialCoherence.overlap n m) (theta : ℝ) :
    ((ActualSignedStageControls.parameters l).exactBlock ActualInitialization.geometry.strip
      (request B u)).oscillatoryPressure n (x,theta) =
    (bandVelocityScale h n m * bandVelocityScale h n m) *
      ((ActualSignedStageControls.parameters l).exactBlock ActualInitialization.geometry.strip
        (request B u)).oscillatoryPressure m (bandChartEquiv h n m k x,theta) := by
  let C := (copies l u).commonCorrected fullStrip (ActualSignedStageControls.directions B)
  let a := (ActualSignedStageControls.parameters l).angularFrequency
  have hp : C.pressure n (x,0) = (bandVelocityScale h n m * bandVelocityScale h n m) •
      C.pressure m (bandChartEquiv h n m k x,0) :=
    common_pressure_of_request l u n m k hi (x,0) (fullRequest_transport u H hfixed n m k hi HS
        (x,0) hx)
  have hmode : a n = a m := rfl
  have hphase := carrier_transport l n m k hi (x,0)
  change (SignedWaveUpdate.blockOfCoefficients C a).oscillatoryPressure n (x,theta) =
    (bandVelocityScale h n m * bandVelocityScale h n m) *
      (SignedWaveUpdate.blockOfCoefficients C a).oscillatoryPressure m (bandChartEquiv h n m k
          x,theta)
  simp only [SignedWaveUpdate.blockOfCoefficients, SignedWaveUpdate.coefficientBlock_pressure]
  change (C.pressure n (x,0) * HarmonicFields.character 1
      ((chartCoefficients l.2 l.1).frequency n * (chartCoefficients l.2 l.1).phase n (x,0) +
        (a n : ℝ) * theta)).re =
    (bandVelocityScale h n m * bandVelocityScale h n m) *
      (C.pressure m (bandChartEquiv h n m k x,0) * HarmonicFields.character 1
        ((chartCoefficients l.2 l.1).frequency m * (chartCoefficients l.2 l.1).phase m (chart n m k
            (x,0)) +
          (a m : ℝ) * theta)).re
  rw [hp, hphase, hmode]
  simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring
end NavierStokes.ActualSignedCoherence

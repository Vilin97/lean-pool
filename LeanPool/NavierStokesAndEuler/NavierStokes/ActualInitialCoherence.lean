/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualBaseResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.RankStateCoherence
public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectionInitialization
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPrimaryCoherence
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPrimaryCovariance
import LeanPool.NavierStokesAndEuler.NavierStokes.MeanStageRegularity
import LeanPool.NavierStokesAndEuler.NavierStokes.TemporalStateCoherence

/-!
# Coherence of the literal initialized state

The state here uses the same active primary labels, physical base error,
common gauge, and actual temporal/rank constructors as initialization.
-/

@[expose] public section


namespace NavierStokes.ActualInitialCoherence

noncomputable section

open Set Function Filter
open scoped ContDiff Topology BigOperators
open CorrectionState MeanIncrementBounds MeanStateRegularity PhysicalResidualNaturality


/-- Plane: an abbreviation for `PressureStream.Plane`. -/
abbrev Plane := PressureStream.Plane
/-- Point: an abbreviation for `PressureStream.Lift Plane`. -/
abbrev Point := PressureStream.Lift Plane

/-- Pieces, defined pointwise by `CorrectionInitialization.ActualPrimary.piece
CorrectionInitialization.ActualPrimary.standardRegion l.2 l.1`. -/
noncomputable def pieces (B N0 : ℕ) :
    CorrectionInitialization.ActualPrimary.Label B N0 × Fin 2 →
        CorrectionInitialization.PrimaryPiece (Point × ℝ) :=
  fun l => CorrectionInitialization.ActualPrimary.piece
      CorrectionInitialization.ActualPrimary.standardRegion l.2 l.1

/-- Base error, constructed using `ActualBaseResidual.baseError`. -/
noncomputable def baseError (B : ℕ) : Oscillation Point :=
  ActualBaseResidual.baseError CorrectionInitialization.ActualPrimary.certificate
      CorrectionInitialization.ActualPrimary.modulation
          CorrectionInitialization.ActualPrimary.upper B

/-- Seed, constructed using `CorrectionInitialization.bandSeed`. -/
noncomputable def seed (B N0 : ℕ) : State Point :=
  CorrectionInitialization.bandSeed (CorrectionInitialization.ActualPrimary.activeLabels
      CorrectionInitialization.ActualPrimary.standardRegion B N0) (pieces B N0) (baseError B)

/-- Primary, constructed using `CorrectionInitialization.GaugeInitialization.primaryBands`. -/
noncomputable def primary (B N0 : ℕ) : State Point :=
  CorrectionInitialization.GaugeInitialization.primaryBands
      CorrectionInitialization.ActualPrimary.commonGauge
          (CorrectionInitialization.ActualPrimary.commonContext B)
    (CorrectionInitialization.ActualPrimary.activeLabels
        CorrectionInitialization.ActualPrimary.standardRegion B N0) (pieces B N0) (baseError B)

/-- Temporal, constructed using `CorrectionInitialization.GaugeInitialization.temporalBands`. -/
noncomputable def temporal (B N0 : ℕ) : State Point :=
  CorrectionInitialization.GaugeInitialization.temporalBands
      CorrectionInitialization.ActualPrimary.commonGauge CorrectionInitialization.ActualPrimary.h
          (CorrectionInitialization.CommonWindow.index CorrectionInitialization.ActualPrimary.h)
              ((0,1),0) (CorrectionInitialization.ActualPrimary.commonContext B)
    (CorrectionInitialization.ActualPrimary.activeLabels
        CorrectionInitialization.ActualPrimary.standardRegion B N0) (pieces B N0) (baseError B)

/-- Ranked, constructed using `CorrectionInitialization.GaugeInitialization.rankBands`. -/
noncomputable def ranked (B N0 : ℕ) : State Point :=
  CorrectionInitialization.GaugeInitialization.rankBands
      CorrectionInitialization.ActualPrimary.commonGauge
          CorrectionInitialization.ActualPrimary.rankData CorrectionInitialization.ActualPrimary.h
              (CorrectionInitialization.CommonWindow.index
                  CorrectionInitialization.ActualPrimary.h) ((0,1),0)
                      (CorrectionInitialization.ActualPrimary.commonContext B)
    (CorrectionInitialization.ActualPrimary.activeLabels
        CorrectionInitialization.ActualPrimary.standardRegion B N0) (pieces B N0) (baseError B)

/-- Initialized, constructed using
`CorrectionInitialization.GaugeInitialization.initializedBands`. -/
noncomputable def initialized (B N0 : ℕ) : State Point :=
  CorrectionInitialization.GaugeInitialization.initializedBands
      CorrectionInitialization.ActualPrimary.commonGauge
          CorrectionInitialization.ActualPrimary.rankData CorrectionInitialization.ActualPrimary.h
              (CorrectionInitialization.CommonWindow.index
                  CorrectionInitialization.ActualPrimary.h) ((0,1),0)
                      (CorrectionInitialization.ActualPrimary.commonContext B)
    (CorrectionInitialization.ActualPrimary.activeLabels
        CorrectionInitialization.ActualPrimary.standardRegion B N0) (pieces B N0) (baseError B)

theorem commonGauge_eq_similarity :
    CorrectionInitialization.ActualPrimary.commonGauge = VariableGaugeMean.similarityGauge
        CorrectionInitialization.ActualPrimary.h (ChartScales.radialExponent
            CorrectionInitialization.ActualPrimary.h)
      (PrimaryTargetBounds.leftRadius CorrectionInitialization.ActualPrimary.nominal)
          (PrimaryTargetBounds.rightRadius CorrectionInitialization.ActualPrimary.nominal)
      1 (PrimaryTargetBounds.radii_ordered CorrectionInitialization.ActualPrimary.nominal)
          (CorrectionInitialization.CommonWindow.index CorrectionInitialization.ActualPrimary.h) :=
              by
  simp only [CorrectionInitialization.ActualPrimary.commonGauge, VariableGaugeMean.similarityGauge,
      CommonBaseContext.reconstruction,
    MeanChartCompatibility.radialFrequency, one_mul]
  rfl

theorem slowCoordinates_band (n m k : ℕ) (x : Point) :
    BaseContextAssembly.slowCoordinates (GaugeStateCoherence.bandChartEquiv
        CorrectionInitialization.ActualPrimary.h n m k x) =
      SimilarityHomogeneity.chartTransition CorrectionInitialization.ActualPrimary.h (ChartScales.Q
          n) (ChartScales.Q m) (BaseContextAssembly.slowCoordinates x) := rfl

theorem physicalPoint_band (n m k : ℕ) (x : Point) :
    BaseContextAssembly.physicalPoint CorrectionInitialization.ActualPrimary.h m
        (GaugeStateCoherence.bandChartEquiv CorrectionInitialization.ActualPrimary.h n m k x) =
            BaseContextAssembly.physicalPoint CorrectionInitialization.ActualPrimary.h n x := by
  rw [← ActualBaseResidual.physicalPoint_zero_angle, ← ActualBaseResidual.physicalPoint_zero_angle,
    ActualBaseResidual.physicalPoint_bandChart]

theorem normalizedCoordinates_band (n m k : ℕ) {x : Point} (hT : 0 < x.2.1.1) :
    BaseChartJets.normalizedCoordinates CorrectionInitialization.ActualPrimary.h
        (BaseContextAssembly.slowCoordinates (GaugeStateCoherence.bandChartEquiv
            CorrectionInitialization.ActualPrimary.h n m k x)) =
      SlowBorelBase.scaleMap (ChartScales.Q n / ChartScales.Q m)
        (BaseChartJets.normalizedCoordinates CorrectionInitialization.ActualPrimary.h
            (BaseContextAssembly.slowCoordinates x)) := by
  rw [slowCoordinates_band, BaseChartJets.normalizedCoordinates_eq,
      BaseChartJets.normalizedCoordinates_eq,
    SimilarityHomogeneity.chartQ_transition
        CorrectionInitialization.ActualPrimary.outgoing.data.h_pos
            CorrectionInitialization.ActualPrimary.outgoing.data.h_lt_half
      (ChartScales.Q_pos n) (ChartScales.Q_pos m) hT,
    SimilarityHomogeneity.chartX_transition
        CorrectionInitialization.ActualPrimary.outgoing.data.h_pos
            CorrectionInitialization.ActualPrimary.outgoing.data.h_lt_half
      (ChartScales.Q_pos n) (ChartScales.Q_pos m) hT,
    SimilarityHomogeneity.chartEta_transition
        CorrectionInitialization.ActualPrimary.outgoing.data.h_pos
            CorrectionInitialization.ActualPrimary.outgoing.data.h_lt_half
      (ChartScales.Q_pos n) (ChartScales.Q_pos m) hT]
  rfl

theorem scaledCoordinates_band (n m k : ℕ) {x : Point} (hT : 0 < x.2.1.1) :
    SlowBorelBase.scaleMap (ChartScales.Q m)
        (BaseChartJets.normalizedCoordinates CorrectionInitialization.ActualPrimary.h
            (BaseContextAssembly.slowCoordinates (GaugeStateCoherence.bandChartEquiv
                CorrectionInitialization.ActualPrimary.h n m k x))) =
      SlowBorelBase.scaleMap (ChartScales.Q n) (BaseChartJets.normalizedCoordinates
          CorrectionInitialization.ActualPrimary.h (BaseContextAssembly.slowCoordinates x)) := by
  rw [normalizedCoordinates_band n m k hT]
  apply Prod.ext
  · change ChartScales.Q m * ((ChartScales.Q n / ChartScales.Q m) * _) = ChartScales.Q n * _
    field_simp [(ChartScales.Q_pos m).ne']
  · rfl

theorem axialFactor_band (n m k : ℕ) {x : Point} (hT : 0 < x.2.1.1) :
    GaugeStateCoherence.bandVelocityScale CorrectionInitialization.ActualPrimary.h n m *
        BaseChartJets.axialFactor CorrectionInitialization.ActualPrimary.h
            (BaseContextAssembly.slowCoordinates (GaugeStateCoherence.bandChartEquiv
                CorrectionInitialization.ActualPrimary.h n m k x)) =
      BaseChartJets.axialFactor CorrectionInitialization.ActualPrimary.h
          (BaseContextAssembly.slowCoordinates x) := by
  have hr := div_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m)
  have hq := BaseChartJets.normalizedCoordinates_q_pos
      CorrectionInitialization.ActualPrimary.outgoing.data.h_pos
          CorrectionInitialization.ActualPrimary.outgoing.data.h_lt_half (p :=
              BaseContextAssembly.slowCoordinates x) hT
  simp only [BaseChartJets.axialFactor, normalizedCoordinates_band n m k hT,
      SlowBorelBase.scaleMap_apply,
    Real.mul_rpow hr.le hq.le, GaugeStateCoherence.bandVelocityScale]
  rw [← mul_assoc, ← Real.rpow_add hr, add_neg_cancel, Real.rpow_zero, one_mul]

theorem context_radial_band (B n m k : ℕ) (x : Point) :
    (CorrectionInitialization.ActualPrimary.commonContext B).base.radial n x =
        GaugeStateCoherence.bandVelocityScale CorrectionInitialization.ActualPrimary.h n m *
      (CorrectionInitialization.ActualPrimary.commonContext B).base.radial m
          (GaugeStateCoherence.bandChartEquiv CorrectionInitialization.ActualPrimary.h n m k x) :=
              by
  change ChartScales.Q n ^ CoordinateAlgebra.A CorrectionInitialization.ActualPrimary.h * _ =
    GaugeStateCoherence.bandVelocityScale CorrectionInitialization.ActualPrimary.h n m *
        (ChartScales.Q m ^ CoordinateAlgebra.A CorrectionInitialization.ActualPrimary.h * _)
  rw [physicalPoint_band]
  rw [← mul_assoc, mul_comm (GaugeStateCoherence.bandVelocityScale
      CorrectionInitialization.ActualPrimary.h n m)]
  simp only [GaugeStateCoherence.bandVelocityScale, ActualBaseResidual.band_power_product]

theorem context_axial_band (B n m k : ℕ) {x : Point} (hT : 0 < x.2.1.1) :
    (CorrectionInitialization.ActualPrimary.commonContext B).base.axial n x =
        GaugeStateCoherence.bandVelocityScale CorrectionInitialization.ActualPrimary.h n m *
      (CorrectionInitialization.ActualPrimary.commonContext B).base.axial m
          (GaugeStateCoherence.bandChartEquiv CorrectionInitialization.ActualPrimary.h n m k x) :=
              by
  change BaseChartJets.axial _ _ _ _ _ = GaugeStateCoherence.bandVelocityScale
      CorrectionInitialization.ActualPrimary.h n m * BaseChartJets.axial _ _ _ _ _
  simp only [BaseChartJets.axial]
  rw [scaledCoordinates_band n m k hT, ← mul_assoc, axialFactor_band n m k hT]

theorem context_angular_band (B n m k : ℕ) {x : Point} (hT : 0 < x.2.1.1) :
    (CorrectionInitialization.ActualPrimary.commonContext B).base.angular n x =
        GaugeStateCoherence.bandVelocityScale CorrectionInitialization.ActualPrimary.h n m *
      (CorrectionInitialization.ActualPrimary.commonContext B).base.angular m
          (GaugeStateCoherence.bandChartEquiv CorrectionInitialization.ActualPrimary.h n m k x) :=
              by
  change x.1 * BaseChartJets.frequency _ _ _ _ _ _ = GaugeStateCoherence.bandVelocityScale
      CorrectionInitialization.ActualPrimary.h n m *
    ((GaugeStateCoherence.bandChartEquiv CorrectionInitialization.ActualPrimary.h n m k x).1 *
        BaseChartJets.frequency _ _ _ _ _ _)
  simp only [BaseChartJets.frequency, BaseChartJets.frequencyFactor]
  rw [scaledCoordinates_band n m k hT]
  by_cases hR : x.1 = 0
  · simp only [GaugeStateCoherence.bandChartEquiv_apply, hR, mul_zero, zero_mul,
      BaseContextAssembly.slowCoordinates_apply, div_zero]
  · have hR' : (GaugeStateCoherence.bandChartEquiv CorrectionInitialization.ActualPrimary.h n m k
      x).1 ≠ 0 :=
      mul_ne_zero (GaugeStateCoherence.bandScale_pos n m).ne' hR
    have hfactor := axialFactor_band n m k hT
    change x.1 * (_ / x.1 * _) = _ * ((GaugeStateCoherence.bandChartEquiv
        CorrectionInitialization.ActualPrimary.h n m k x).1 *
      (_ / (GaugeStateCoherence.bandChartEquiv CorrectionInitialization.ActualPrimary.h n m k x).1
          * _))
    have cancel (R F A : ℝ) (hR : R ≠ 0) : R * (F / R * A) = F * A := by
      field_simp
    rw [cancel _ _ _ hR, cancel _ _ _ hR', ← mul_assoc, hfactor]

theorem stressScale (n m : ℕ) :
    GaugeStateCoherence.bandVelocityScale CorrectionInitialization.ActualPrimary.h n m *
        GaugeStateCoherence.bandVelocityScale CorrectionInitialization.ActualPrimary.h n m *
      ChartScales.Q m ^ (2 * CoordinateAlgebra.A CorrectionInitialization.ActualPrimary.h) =
        ChartScales.Q n ^ (2 * CoordinateAlgebra.A CorrectionInitialization.ActualPrimary.h) := by
  unfold GaugeStateCoherence.bandVelocityScale
  rw [← Real.rpow_add (div_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m)),
    ← two_mul, mul_comm, ActualBaseResidual.band_power_product]

theorem context_stress_band (B n m k : ℕ) (x : Point) :
    BaseContextAssembly.virtualStress CorrectionInitialization.ActualPrimary.certificate
        CorrectionInitialization.ActualPrimary.modulation
            CorrectionInitialization.ActualPrimary.upper B n x =
      (GaugeStateCoherence.bandVelocityScale CorrectionInitialization.ActualPrimary.h n m *
          GaugeStateCoherence.bandVelocityScale CorrectionInitialization.ActualPrimary.h n m) •
        BaseContextAssembly.virtualStress CorrectionInitialization.ActualPrimary.certificate
            CorrectionInitialization.ActualPrimary.modulation
                CorrectionInitialization.ActualPrimary.upper B m
                    (GaugeStateCoherence.bandChartEquiv CorrectionInitialization.ActualPrimary.h n
                        m k x) := by
  by_cases hR : 0 < x.1
  · have hR' : 0 < (GaugeStateCoherence.bandChartEquiv CorrectionInitialization.ActualPrimary.h n m
      k x).1 := mul_pos (GaugeStateCoherence.bandScale_pos n m) hR
    rw [BaseContextAssembly.virtualStress_eq_raw _ _ _ _ _ hR,
        BaseContextAssembly.virtualStress_eq_raw _ _ _ _ _ hR']
    simp only [BaseContextAssembly.rawStress, physicalPoint_band, smul_smul, stressScale]
  · have hR' : (GaugeStateCoherence.bandChartEquiv CorrectionInitialization.ActualPrimary.h n m k
      x).1 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (GaugeStateCoherence.bandScale_pos n m).le (le_of_not_gt hR)
    rw [BaseContextAssembly.virtualStress_eq_zero _ _ _ _ _ (le_of_not_gt hR),
      BaseContextAssembly.virtualStress_eq_zero _ _ _ _ _ hR', smul_zero]

section CommonContext

open CorrectionInitialization.ActualPrimary GaugeStateCoherence

theorem commonGauge_on {V : Set Plane} (htime : ∀ s ∈ V, 0 < s.1)
    (n m k : ℕ) (hi : CorrectionInitialization.CommonWindow.index h n + k =
      CorrectionInitialization.CommonWindow.index h m) :
    GaugeOn V (bandScale n m) (bandSlowEquiv h n m).toContinuousLinearMap k
      commonGauge commonGauge n m := by
  rw [commonGauge_eq_similarity]
  exact similarityGaugeOn outgoing.data.h_pos outgoing.data.h_lt_half _ _ _ _ _ _ n m k hi htime

theorem frame_radial (B n : ℕ) (x : Point) :
    (HarmonicResidual.contextFrame (commonContext B) n).radial x =
      PressureStream.radialVector
        (PressureStream.physicalSpeed commonGauge.radial.exponent (commonGauge.radial.frequency n))
        ((0 : Plane), commonGauge.radial.radialDirection) x := by
  change (1, ((0 : Plane), (0 : Plane))) +
      (commonGauge.radial.frequency n * RadialPullback.radialJacobian commonGauge.radial.exponent
          x.1) •
        (0, ((0 : Plane), commonGauge.radial.radialDirection)) =
    (1, (RadialPullback.radialJacobian commonGauge.radial.exponent x.1 *
        commonGauge.radial.frequency n) •
      ((0 : Plane), commonGauge.radial.radialDirection))
  simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, zero_add, mul_comm]

theorem viscosity_scale (n m : ℕ) :
    ChartScales.epsilon h n * bandScale n m = bandVelocityScale h n m * ChartScales.epsilon h m :=
        by
  rw [bandScale_eq_ratioPower, bandVelocityScale_eq_ratioPower]
  exact PhysicalResidualNaturality.weight_viscosity (ChartScales.Q_pos n) (ChartScales.Q_pos m) h

theorem slowTime_scalar (n m : ℕ) :
    (ChartScales.Q n / ChartScales.Q m) * ChartScales.epsilon h n =
      (bandVelocityScale h n m * bandScale n m) * ChartScales.epsilon h m := by
  have hsq : bandScale n m * bandScale n m = ChartScales.Q n / ChartScales.Q m := by
    unfold bandScale
    rw [← Real.rpow_add (div_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m))]
    norm_num
  calc
    _ = bandScale n m * (ChartScales.epsilon h n * bandScale n m) := by rw [← hsq]; ring
    _ = _ := by rw [viscosity_scale]; ring

theorem slowTime_vector (n m k : ℕ) :
    bandChartEquiv h n m k (ChartScales.epsilon h n • ((0, ((1,0),0)) : Point)) =
      (bandVelocityScale h n m * bandScale n m) •
        (ChartScales.epsilon h m • ((0, ((1,0),0)) : Point)) := by
  ext <;> simp only [bandChartEquiv_apply, bandSlowEquiv_apply, Prod.smul_mk,
    smul_eq_mul, mul_zero, mul_one, map_zero, smul_zero]
  exact slowTime_scalar n m

theorem context_frame_band (B : ℕ) {V : Set Plane} (htime : ∀ s ∈ V, 0 < s.1)
    (n m k : ℕ) (hi : CorrectionInitialization.CommonWindow.index h n + k =
      CorrectionInitialization.CommonWindow.index h m) :
    FrameOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv h n m k)
      (bandVelocityScale h n m) (bandScale n m)
      (HarmonicResidual.contextFrame (commonContext B) n)
      (HarmonicResidual.contextFrame (commonContext B) m) := by
  have hg := commonGauge_on htime n m k hi
  refine ⟨?_, ?_, ?_, fun _ _ => rfl, viscosity_scale n m⟩
  · intro x hx
    rw [frame_radial, frame_radial, bandChartEquiv_apply]
    apply Prod.ext
    · simp [PressureStream.radialVector]
    · change ((bandSlowEquiv h n m).toContinuousLinearMap.prodMap (TemporalMeanUpdate.coverMap k))
        (PressureStream.physicalSpeed commonGauge.radial.exponent (commonGauge.radial.frequency n)
            x.1 •
          ((0 : Plane), commonGauge.radial.radialDirection)) =
        bandScale n m • (PressureStream.physicalSpeed commonGauge.radial.exponent
          (commonGauge.radial.frequency m) (bandScale n m * x.1) •
            ((0 : Plane), commonGauge.radial.radialDirection))
      apply TemporalStateCoherence.physicalSpeed_vector_all (bandScale_pos n m)
      apply Prod.ext
      · simp
      · exact hg.frequency
  · intro x hx
    change bandChartEquiv h n m k
      (ChartScales.epsilon h n • ((0, ((0,1),0)) : Point)) =
        bandScale n m • (ChartScales.epsilon h m • ((0, ((0,1),0)) : Point))
    apply Prod.ext
    · simp [bandChartEquiv_apply]
    · have he := TemporalStateCoherence.band_axial_transport h n m k
      simp only [bandChartEquiv_apply, Prod.smul_mk] at he ⊢
      exact he
  · intro x hx
    change bandChartEquiv h n m k
      ((commonContext B).operators.fastCoefficient n • (commonContext B).operators.vT -
        ChartScales.epsilon h n • ((0, ((1,0),0)) : Point)) =
      (bandVelocityScale h n m * bandScale n m) •
        ((commonContext B).operators.fastCoefficient m • (commonContext B).operators.vT -
          ChartScales.epsilon h m • ((0, ((1,0),0)) : Point))
    rw [map_sub, smul_sub, slowTime_vector]
    congr 1
    exact TemporalStateCoherence.common_fast_transport h
        (CorrectionInitialization.CommonWindow.index h)
      _ _ (PrimaryTargetBounds.radii_ordered nominal) n m k hi

theorem context_band (B : ℕ) {V : Set Plane} (htime : ∀ s ∈ V, 0 < s.1)
    (n m k : ℕ) (hi : CorrectionInitialization.CommonWindow.index h n + k =
      CorrectionInitialization.CommonWindow.index h m) :
    ContextOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv h n m k)
      (bandVelocityScale h n m) (bandScale n m) (commonContext B) (commonContext B) n m := by
  refine ⟨context_frame_band B htime n m k hi, ?_, ?_, ?_⟩
  · exact ⟨fun x _ => context_radial_band B n m k x,
      fun x hx => context_angular_band B n m k (htime _ hx),
      fun x hx => context_axial_band B n m k (htime _ hx)⟩
  · intro x hx
    exact congrArg Prod.fst (context_stress_band B n m k x)
  · intro x hx
    exact congrArg Prod.snd (context_stress_band B n m k x)

end CommonContext

section PrimitiveStages

open CorrectionInitialization.ActualPrimary GaugeStateCoherence

theorem primary_primitive_of_seed (B N0 : ℕ)
    (H : PrimitiveData standardRegion commonGauge.radial.inner commonGauge.radial.outer
      (commonContext B) (seed B N0)) :
    PrimitiveData standardRegion commonGauge.radial.inner commonGauge.radial.outer
      (commonContext B) (primary B N0) :=
  ⟨H.operators, H.base, H.mean, H.covariance, H.virtualTheta, H.virtualAxial⟩

theorem temporal_primitive_of_seed (B N0 : ℕ)
    (H : PrimitiveData standardRegion commonGauge.radial.inner commonGauge.radial.outer
      (commonContext B) (seed B N0)) :
    PrimitiveData standardRegion commonGauge.radial.inner commonGauge.radial.outer
      (commonContext B) (temporal B N0) :=
  MeanStageRegularity.temporalStage_primitive (primary_primitive_of_seed B N0 H)
    (PrimaryTargetBounds.leftRadius_pos nominal)
    (ChartScales.radialExponent_pos h outgoing.data.h_pos.le)
    commonGauge_length rfl h (CorrectionInitialization.CommonWindow.index h) ((0,1),0)

theorem rank_geometry_of_primitive (B : ℕ) (u : State Point)
    (H : PrimitiveData standardRegion commonGauge.radial.inner commonGauge.radial.outer
        (commonContext B) u) :
    LocalRankDefect.RankGeometry commonGauge rankData standardRegion.carrier (commonContext B) u :=
  rank_geometry standardRegion B u (MeanStageRegularity.debt_smooth H
    (PrimaryTargetBounds.leftRadius_pos nominal) (PrimaryTargetBounds.radii_ordered nominal))

theorem ranked_primitive_of_seed (B N0 : ℕ)
    (H : PrimitiveData standardRegion commonGauge.radial.inner commonGauge.radial.outer
      (commonContext B) (seed B N0)) :
    PrimitiveData standardRegion commonGauge.radial.inner commonGauge.radial.outer
      (commonContext B) (ranked B N0) :=
  MeanStageRegularity.rankStage_primitive (temporal_primitive_of_seed B N0 H)
    (rank_geometry_of_primitive B (temporal B N0) (temporal_primitive_of_seed B N0 H))
    commonGauge_length ((0,1),0)

theorem initialized_primitive_of_seed (B N0 : ℕ)
    (H : PrimitiveData standardRegion commonGauge.radial.inner commonGauge.radial.outer
      (commonContext B) (seed B N0)) :
    PrimitiveData standardRegion commonGauge.radial.inner commonGauge.radial.outer
      (commonContext B) (initialized B N0) := by
  have hh := ranked_primitive_of_seed B N0 H
  exact ⟨hh.operators, hh.base, hh.mean, hh.covariance, hh.virtualTheta, hh.virtualAxial⟩

theorem initialized_reconstructed (B N0 : ℕ) :
    VariableGaugeMean.reconstructState commonGauge (commonContext B) (initialized B N0) =
        initialized B N0 := rfl

theorem debtRegular_of_primitive (B : ℕ) (u : State Point)
    (H : PrimitiveData standardRegion commonGauge.radial.inner commonGauge.radial.outer
        (commonContext B) u)
    (n : ℕ) : RankStateCoherence.DebtRegular standardRegion.carrier (commonContext B) u n := by
  have hr := H.source (PrimaryTargetBounds.leftRadius_pos nominal)
      (PrimaryTargetBounds.radii_ordered nominal)
  have ht := (H.angular_flux (PrimaryTargetBounds.leftRadius_pos nominal)
    (PrimaryTargetBounds.radii_ordered nominal)).axial
  have hz := (H.axial_flux (PrimaryTargetBounds.leftRadius_pos nominal)
    (PrimaryTargetBounds.radii_ordered nominal)).axial
  exact ⟨hr.smooth n, ht.smooth n, hz.smooth n, hr.periodic n, ht.periodic n, hz.periodic n⟩

end PrimitiveStages

section TransportStages

open CorrectionInitialization.ActualPrimary GaugeStateCoherence

variable (B N0 n m k : ℕ)
    (hi : CorrectionInitialization.CommonWindow.index h n + k =
        CorrectionInitialization.CommonWindow.index h m)
    {V : Set Plane} (hV : IsOpen V) (hsub : V ⊆ standardRegion.carrier)
    (hmap : MapsTo (bandSlowEquiv h n m) V standardRegion.carrier)
    (HP : PrimitiveData standardRegion commonGauge.radial.inner commonGauge.radial.outer
      (commonContext B) (seed B N0))
    (HS : StateOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv h n m k)
      (bandVelocityScale h n m) (bandScale n m) (seed B N0) (seed B N0) n m)

include hi hV hsub hmap HP HS

theorem primary_band_of_seed :
    StateOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv h n m k)
      (bandVelocityScale h n m) (bandScale n m) (primary B N0) (primary B N0) n m := by
  have ht : ∀ s ∈ V, 0 < s.1 := fun s hs => standardRegion.time_pos s (hsub hs)
  have hr := HP.source (PrimaryTargetBounds.leftRadius_pos nominal)
      (PrimaryTargetBounds.radii_ordered nominal)
  exact reconstructState_on (bandScale_pos n m) (bandSlowEquiv h n m) k
    hV standardRegion.isOpen hmap commonGauge commonGauge (commonContext B) (commonContext B)
    (seed B N0) (seed B N0) n m (PrimaryTargetBounds.leftRadius_pos nominal)
    (ChartScales.radialExponent_pos h outgoing.data.h_pos.le) (commonGauge_on ht n m k hi)
    HS (context_band B ht n m k hi) (hr.smooth m) (hr.periodic m) (hr.supported m)

theorem temporal_band_of_seed :
    StateOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv h n m k)
      (bandVelocityScale h n m) (bandScale n m) (temporal B N0) (temporal B N0) n m := by
  have ht : ∀ s ∈ V, 0 < s.1 := fun s hs => standardRegion.time_pos s (hsub hs)
  have hP := primary_primitive_of_seed B N0 HP
  have hθ := hP.theta (PrimaryTargetBounds.leftRadius_pos nominal)
      (PrimaryTargetBounds.radii_ordered nominal)
  have hz := hP.axial_reconstructed (PrimaryTargetBounds.leftRadius_pos nominal)
    (ChartScales.radialExponent_pos h outgoing.data.h_pos.le) commonGauge_length rfl
  have hpost := (temporal_primitive_of_seed B N0 HP).source
    (PrimaryTargetBounds.leftRadius_pos nominal) (PrimaryTargetBounds.radii_ordered nominal)
  exact TemporalStateCoherence.temporalStage_on (bandScale_pos n m) (bandSlowEquiv h n m) k
    hV standardRegion.isOpen hmap commonGauge commonGauge (commonContext B) (commonContext B)
    (primary B N0) (primary B N0) h (CorrectionInitialization.CommonWindow.index h)
    (CorrectionInitialization.CommonWindow.index h) n m (PrimaryTargetBounds.leftRadius_pos nominal)
    (ChartScales.radialExponent_pos h outgoing.data.h_pos.le) (commonGauge_on ht n m k hi)
    (primary_band_of_seed B N0 n m k hi hV hsub hmap HP HS) (context_band B ht n m k hi)
    (TemporalStateCoherence.clock_band_transport h n m _ _ k hi)
    (hz.smooth m) (hz.periodic m) (hz.supported m) ((0,1),0) ((0,1),0)
    (TemporalStateCoherence.band_axial_transport h n m k) (hθ.smooth m) (hθ.periodic m)
    (TemporalStateCoherence.common_fast_transport h (CorrectionInitialization.CommonWindow.index h)
      _ _ (PrimaryTargetBounds.radii_ordered nominal) n m k hi)
    (hpost.smooth m) (hpost.periodic m) (hpost.supported m)

theorem ranked_band_of_seed :
    StateOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv h n m k)
      (bandVelocityScale h n m) (bandScale n m) (ranked B N0) (ranked B N0) n m := by
  have ht : ∀ s ∈ V, 0 < s.1 := fun s hs => standardRegion.time_pos s (hsub hs)
  have hT := temporal_primitive_of_seed B N0 HP
  have hpost := (ranked_primitive_of_seed B N0 HP).source
    (PrimaryTargetBounds.leftRadius_pos nominal) (PrimaryTargetBounds.radii_ordered nominal)
  exact RankStateCoherence.rankStageState_on (bandScale_pos n m)
    (Real.rpow_pos_of_pos (div_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m)) _).ne'
    (bandSlowEquiv h n m) k hV standardRegion.isOpen hmap
    (temporal_band_of_seed B N0 n m k hi hV hsub hmap HP HS) (context_band B ht n m k hi)
    (debtRegular_of_primitive B (temporal B N0) hT m)
    (RankStateCoherence.normalized_rank_on outgoing.data.h_pos outgoing.data.h_lt_half
      rankAmplitude outgoing.data.core.lam rankInner rankOuter n m ht)
    (commonGauge_on ht n m k hi) (rank_geometry_of_primitive B (temporal B N0) hT)
    ((0,1),0) ((0,1),0) (TemporalStateCoherence.band_axial_transport h n m k)
    (hpost.smooth m) (hpost.periodic m) (hpost.supported m)

theorem initialized_band_of_seed :
    StateOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv h n m k)
      (bandVelocityScale h n m) (bandScale n m) (initialized B N0) (initialized B N0) n m := by
  have ht : ∀ s ∈ V, 0 < s.1 := fun s hs => standardRegion.time_pos s (hsub hs)
  have hR := ranked_band_of_seed B N0 n m k hi hV hsub hmap HP HS
  have hpost := (ranked_primitive_of_seed B N0 HP).source
    (PrimaryTargetBounds.leftRadius_pos nominal) (PrimaryTargetBounds.radii_ordered nominal)
  have halias := pressureAliasState_on (bandScale_pos n m) (bandSlowEquiv h n m) k
    hV standardRegion.isOpen hmap commonGauge commonGauge (commonContext B) (commonContext B)
    (ranked B N0) (ranked B N0) n m (PrimaryTargetBounds.leftRadius_pos nominal)
    (ChartScales.radialExponent_pos h outgoing.data.h_pos.le) (commonGauge_on ht n m k hi)
    hR (context_band B ht n m k hi) (hpost.smooth m) (hpost.periodic m) (hpost.supported m)
  refine ⟨hR.mean, hR.pressure, hR.oscillation, hR.oscillatoryPressure, hR.baseError, hR.gaussian,
      ?_⟩
  intro x hx θ i
  change (ranked B N0).errors.aliasError n (x,θ) i +
    VariableGaugeMean.pressureAliasState commonGauge (commonContext B) (ranked B N0) n (x,θ) i =
      (bandVelocityScale h n m * bandVelocityScale h n m * bandScale n m) *
        ((ranked B N0).errors.aliasError m (bandChartEquiv h n m k x,θ) i +
          VariableGaugeMean.pressureAliasState commonGauge (commonContext B) (ranked B N0) m
            (bandChartEquiv h n m k x,θ) i)
  rw [hR.aliasError x hx θ i, halias x hx θ i, mul_add]
  rfl

end TransportStages

section SeedRegularity

open CorrectionInitialization.ActualPrimary GaugeStateCoherence

theorem common_operator_data (B : ℕ) :
    OperatorData standardRegion.carrier (commonContext B).operators := by
  refine ⟨CommonBaseContext.context_operators_local certificate modulation upper B
    standardRegion.carrier (CorrectionInitialization.CommonWindow.index h), ?_⟩
  intro n R hR s hs Y k
  rfl

theorem common_base_data (B : ℕ) :
    BaseData standardRegion.carrier (commonContext B).base := by
  have hh := CommonBaseContext.context_isSlow certificate modulation upper B
    standardRegion.carrier (CorrectionInitialization.CommonWindow.index h)
  refine ⟨CommonBaseContext.context_base_smooth certificate modulation upper B
    standardRegion (CorrectionInitialization.CommonWindow.index h), ?_, ?_, ?_⟩
  · intro n R hR s hs Y k
    exact (hh.1 n R s hs _).trans (hh.1 n R s hs Y).symm
  · intro n R hR s hs Y k
    exact (hh.2.1 n R s hs _).trans (hh.2.1 n R s hs Y).symm
  · intro n R hR s hs Y k
    exact (hh.2.2 n R s hs _).trans (hh.2.2 n R s hs Y).symm

theorem supportedGauge_of_movingSupport {coord a b : ℝ}
    {U : LocalSignedRequest.SlowRegion coord} {f : Point → ℝ}
    (hf : LocalSignedRequest.MovingSupport a b coord U.carrier f) :
    VariableGaugeMean.SupportedGauge a b (VariableGaugeMean.qLength coord) U.carrier f := by
  intro x hx hn
  have he := hf x hx hn
  have hq := VariableGaugeMean.qLength_pos U.coord_pos U.coord_lt_one (U.time_pos _ hx)
  change x.1 / VariableGaugeMean.qLength coord x.2.1 ∈ Icc a b at he
  exact ⟨by simpa only [mul_comm] using (le_div_iff₀ hq).mp he.1,
    by simpa only [mul_comm] using (div_le_iff₀ hq).mp he.2⟩

theorem common_virtual_moving (B : ℕ) :
    GaugeMomentBalances.MovingField standardRegion commonGauge.radial.inner commonGauge.radial.outer
      (commonContext B).virtualTheta ∧
    GaugeMomentBalances.MovingField standardRegion commonGauge.radial.inner commonGauge.radial.outer
      (commonContext B).virtualAxial := by
  have hh := CommonBaseContext.context_stress_properties certificate modulation upper B
    standardRegion (CorrectionInitialization.CommonWindow.index h)
  exact ⟨⟨fun n => (hh n).1.fst, fun n => supportedGauge_of_movingSupport (hh n).2.2.2.1,
      fun n => (hh n).2.1⟩,
    ⟨fun n => (hh n).1.snd, fun n => supportedGauge_of_movingSupport (hh n).2.2.2.2,
      fun n => (hh n).2.2.1⟩⟩

theorem seed_smooth (B N0 : ℕ) :
    WaveStateRegularity.AngularSmooth (PhysicalMeanDomain.slowDomain standardRegion.carrier)
      (seed B N0).oscillation := by
  intro n i
  apply ContDiffOn.sum
  intro l hl
  exact (contDiffOn_pi.mp (ActualPrimaryCoherence.piece_velocity_smooth standardRegion l.2 l.1 n)
      i).mono
    (fun x hx => standardRegion.time_pos _ hx.1)

theorem seed_support (B N0 : ℕ) :
    WaveStateRegularity.WaveSupport standardRegion commonGauge.radial.inner commonGauge.radial.outer
      (seed B N0).oscillation := by
  change WaveStateRegularity.WaveSupport standardRegion
    (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal)
    (LabelSumBounds.fieldSum (activeLabels standardRegion B N0)
      (fun l => (piece standardRegion l.2 l.1).velocity))
  refine WaveStateRegularity.fieldSum_support
    (labels := activeLabels standardRegion B N0)
    (u := fun l : Label B N0 × Fin 2 => (piece standardRegion l.2 l.1).velocity) ?_
  intro n l hl θ i x hx hn
  exact ActualPrimaryCoherence.piece_velocity_support standardRegion l.2 l.1 n
    (x := (x, θ)) (standardRegion.time_pos _ hx) (fun hz => hn (congrFun hz i))

theorem seed_covariance_regular (B N0 : ℕ) (i j : Fin 3) :
    GaugeDebtIncrement.Regular standardRegion commonGauge.radial.inner commonGauge.radial.outer
      ((seed B N0).covariance i j) :=
  WaveStateRegularity.bilinearCovariance_regular standardRegion (seed_smooth B N0)
    (seed_smooth B N0) (seed_support B N0) i j

theorem active_index_le {B N0 n : ℕ} {l : Label B N0 × Fin 2}
    (hl : l ∈ activeLabels standardRegion B N0 n) :
    CorrectionInitialization.CommonWindow.index h n ≤
      ChartScales.nativeIndex h (BaseChartJets.cellBand l.1) := by
  have hm := (mem_activeLabels standardRegion n l.1 l.2).mp hl
  obtain ⟨m, hm, hgrid⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨g, hg, he⟩ := Finset.mem_image.mp hgrid
  apply CorrectionInitialization.CommonWindow.index_le
  have he' := congrArg Prod.fst he
  change m = BaseChartJets.cellBand l.1 at he'
  exact he' ▸ hm

end SeedRegularity

theorem sum_eq_mul_sum_of_support {ι : Type}
    (s t : Finset ι) (f g : ι → ℝ) (a : ℝ)
    (hf : ∀ i, i ∉ s → f i = 0) (hg : ∀ i, i ∉ t → g i = 0)
    (he : ∀ i, f i = a * g i) :
    ∑ i ∈ s, f i = a * ∑ i ∈ t, g i := by
  classical
  have hs : ∑ i ∈ s, f i = ∑ i ∈ s ∪ t, f i :=
    Finset.sum_subset Finset.subset_union_left (fun i _ hi => hf i hi)
  have ht : ∑ i ∈ t, g i = ∑ i ∈ s ∪ t, g i :=
    Finset.sum_subset Finset.subset_union_right (fun i _ hi => hg i hi)
  rw [hs, ht, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => he i)

section IndividualBlocks

open CorrectionInitialization CorrectionInitialization.ActualPrimary GaugeStateCoherence

variable {B N0 : ℕ}

/-- Phase, given by `(pieces B N0 l).coefficients.phase n (x, 0)`. -/
noncomputable def phase (l : Label B N0 × Fin 2) (n : ℕ) (x : Point) : ℝ :=
  (pieces B N0 l).coefficients.phase n (x, 0)

/-- Angular mode, given by `PrimaryGeometryAssembly.angularMode certificate modulation (choice B
N0).prepared l.2 l.1`. -/
noncomputable def angularMode (l : Label B N0 × Fin 2) (_n : ℕ) : ℤ :=
  PrimaryGeometryAssembly.angularMode certificate modulation (choice B N0).prepared l.2 l.1

/-- Primary block, given by `(pieces B N0 l).harmonicBlock (phase l) (angularMode l)`. -/
noncomputable def primaryBlock (l : Label B N0 × Fin 2) : HarmonicBlock Point :=
  (pieces B N0 l).harmonicBlock (phase l) (angularMode l)

/-- Gaussian block, given by `(pieces B N0 l).excludedBlock (phase l) (angularMode l)`. -/
noncomputable def gaussianBlock (l : Label B N0 × Fin 2) : HarmonicBlock Point :=
  (pieces B N0 l).excludedBlock (phase l) (angularMode l)

theorem angularMode_ne (l : Label B N0 × Fin 2) (n : ℕ) : angularMode l n ≠ 0 :=
  PrimaryGeometryAssembly.angularMode_ne_zero certificate modulation (choice B N0).prepared l.2 l.1

theorem phase_split (l : Label B N0 × Fin 2) (n : ℕ) (x : Point) (θ : ℝ) :
    (pieces B N0 l).coefficients.frequency n * (pieces B N0 l).coefficients.phase n (x, θ) =
      (pieces B N0 l).coefficients.frequency n * phase l n x + (angularMode l n : ℝ) * θ := by
  change (chartCoefficients l.2 l.1).frequency n * (chartCoefficients l.2 l.1).phase n (x, θ) =
    (chartCoefficients l.2 l.1).frequency n * (chartCoefficients l.2 l.1).phase n (x, 0) + _
  rw [chartCoefficients_phase, chartCoefficients_phase]
  simp only [CorrectionInitialization.ActualPrimary.absolutePhase, angularMode, mul_zero, zero_add]
  ring

theorem exact_amplitude_angle (l : Label B N0 × Fin 2) :
    ErrorHarmonics.AngleIndependent (pieces B N0 l).exactCoefficients.amplitude := by
  intro n x θ
  exact CopyAngularInvariance.invariant_eq_zeroSlice
    ((chartCoefficients_angular l.2 l.1).corrected_amplitude
      (BaseContextAssembly.nativeStrip nominal standardRegion) (commonContext B) n) x θ

theorem exact_pressure_angle (l : Label B N0 × Fin 2) :
    ErrorHarmonics.AngleIndependent (pieces B N0 l).exactCoefficients.pressure := by
  intro n x θ
  exact CopyAngularInvariance.invariant_eq_zeroSlice
    ((chartCoefficients_angular l.2 l.1).corrected_pressure
      (BaseContextAssembly.nativeStrip nominal standardRegion) (commonContext B) n) x θ

theorem primaryBlock_represents (l : Label B N0 × Fin 2) :
    (primaryBlock l).oscillation = (pieces B N0 l).velocity ∧
      (primaryBlock l).oscillatoryPressure = (pieces B N0 l).pressure :=
  (pieces B N0 l).harmonicBlock_represents (phase l) (angularMode l)
    (exact_amplitude_angle l) (exact_pressure_angle l) (phase_split l)

theorem gaussianBlock_represents (l : Label B N0 × Fin 2) :
    (gaussianBlock l).oscillation = (pieces B N0 l).excluded :=
  (pieces B N0 l).excludedBlock_represents (phase l) (angularMode l)
    (fun n => (periodicGaussian_smooth l.2 l.1).comp
      ((toAbsolute_smooth n).snd.comp contDiff_fst))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (phase_split l)

/-- Exact carrier equality follows from the actual inverse-cover chart map.
Torus periodicity, when needed, uses the separate active-index inequality. -/
theorem block_phase_band (l : Label B N0 × Fin 2) (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m) (x : Point) :
    (primaryBlock l).frequency n * (primaryBlock l).phase n x =
      (primaryBlock l).frequency m * (primaryBlock l).phase m (bandChartEquiv h n m k x) := by
  change (chartCoefficients l.2 l.1).frequency n * (chartCoefficients l.2 l.1).phase n (x, 0) =
    (chartCoefficients l.2 l.1).frequency m * (chartCoefficients l.2 l.1).phase m
      (bandChartEquiv h n m k x, 0)
  rw [chartCoefficients_phase, chartCoefficients_phase, ActualPrimaryCoherence.toAbsolute_bandChart
      n m k hi]

theorem blockFields_band (l : Label B N0 × Fin 2) (U : Set Point) (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m) :
    BlockFieldsOn U (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m)
      (primaryBlock l) (primaryBlock l) (gaussianBlock l).velocity 0
      (gaussianBlock l).velocity 0 n m := by
  refine ⟨fun x _ => block_phase_band l n m k hi x, rfl, angularMode_ne l n, ?_, ?_, ?_, ?_⟩
  · intro x hx θ i
    rw [(primaryBlock_represents l).1]
    exact congrFun (ActualPrimaryCoherence.piece_velocity_band standardRegion l.2 l.1 n m k hi (x,
        θ)) i
  · intro x hx θ
    rw [(primaryBlock_represents l).2]
    exact ActualPrimaryCoherence.piece_pressure_band standardRegion l.2 l.1 n m k hi (x, θ)
  · intro x hx θ i
    change (gaussianBlock l).oscillation n (x, θ) i =
      _ * (gaussianBlock l).oscillation m (bandChartEquiv h n m k x, θ) i
    rw [gaussianBlock_represents]
    exact congrFun (ActualPrimaryCoherence.piece_excluded_band standardRegion l.2 l.1 n m k hi (x,
        θ)) i
  · intro x hx θ i
    simp [HarmonicFields.field]

end IndividualBlocks

section ActualSeed

open CorrectionInitialization.ActualPrimary GaugeStateCoherence

theorem seed_velocity_periodic (B N0 n : ℕ) (R : ℝ) (s : Plane) (θ : ℝ) :
    FourierAlias.TorusPeriodic (fun Y => (seed B N0).oscillation n ((R, (s, Y)), θ)) := by
  intro Y k
  funext i
  apply Finset.sum_congr rfl
  intro l hl
  have he := congrFun (ActualPrimaryCoherence.piece_velocity_periodic standardRegion l.2 l.1 n
    (active_index_le hl) k ((R, (s, Y)), θ)) i
  simp only [ActualPrimaryCoherence.chartDeck, TorusAverages.latticePoint,
    Prod.add_def, add_zero] at he
  exact he

theorem covariance_periodic_of_periodic {U : Set Plane} {u : Oscillation Point}
    (hu : ∀ n θ i, PhysicalMeanDomain.PeriodicOn U (fun x => u n (x, θ) i))
    (i j : Fin 3) : Periodic U (bilinearCovariance u u i j) := by
  intro n R s hs Y k
  change (∫ θ in (0 : ℝ)..2 * Real.pi,
    u n ((R, (s, Y + ((k.1 : ℝ), (k.2 : ℝ)))), θ) i *
      u n ((R, (s, Y + ((k.1 : ℝ), (k.2 : ℝ)))), θ) j) / (2 * Real.pi) =
    (∫ θ in (0 : ℝ)..2 * Real.pi, u n ((R, (s, Y)), θ) i *
      u n ((R, (s, Y)), θ) j) / (2 * Real.pi)
  apply congrArg (fun a : ℝ => a / (2 * Real.pi))
  apply intervalIntegral.integral_congr
  intro θ hθ
  exact congrArg₂ (· * ·) (hu n θ i R s hs Y k) (hu n θ j R s hs Y k)

theorem seed_covariance_periodic (B N0 : ℕ) (i j : Fin 3) :
    Periodic standardRegion.carrier ((seed B N0).covariance i j) :=
  covariance_periodic_of_periodic
    (fun n θ i R s _ Y k => congrFun (seed_velocity_periodic B N0 n R s θ Y k) i) i j

theorem seed_primitive (B N0 : ℕ) :
    PrimitiveData standardRegion commonGauge.radial.inner commonGauge.radial.outer
      (commonContext B) (seed B N0) := by
  refine ⟨common_operator_data B, common_base_data B, ?_, ?_,
    (common_virtual_moving B).1, (common_virtual_moving B).2⟩
  · exact ⟨MovingField.zero, MovingField.zero, MovingField.zero⟩
  · intro i j
    exact MovingField.of_regular (seed_covariance_regular B N0 i j) (seed_covariance_periodic B N0
        i j)

theorem seed_band (B N0 n m k : ℕ)
    (hi : CorrectionInitialization.CommonWindow.index h n + k =
        CorrectionInitialization.CommonWindow.index h m)
    {V : Set Plane} (hsub : V ⊆ standardRegion.carrier)
    (hmap : MapsTo (bandSlowEquiv h n m) V standardRegion.carrier) :
    StateOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv h n m k)
      (bandVelocityScale h n m) (bandScale n m) (seed B N0) (seed B N0) n m := by
  classical
  have hb := ActualBaseResidual.errorState_band certificate modulation upper B
    (PhysicalMeanDomain.slowDomain V) n m k
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, hb.baseError, ?_, ?_⟩
  · intro x hx; simp [seed, CorrectionInitialization.bandSeed]
  · intro x hx; simp [seed, CorrectionInitialization.bandSeed]
  · intro x hx; simp [seed, CorrectionInitialization.bandSeed]
  · intro x hx; simp [seed, CorrectionInitialization.bandSeed]
  · intro x hx θ i
    apply sum_eq_mul_sum_of_support
    · intro l hl
      exact congrFun (ActualPrimaryCovariance.piece_velocity_inactive l n (hsub hx) θ hl) i
    · intro l hl
      exact congrFun (ActualPrimaryCovariance.piece_velocity_inactive l m (hmap hx) θ hl) i
    · intro l
      exact congrFun (ActualPrimaryCoherence.piece_velocity_band standardRegion l.2 l.1 n m k hi
          (x, θ)) i
  · intro x hx θ
    apply sum_eq_mul_sum_of_support
    · intro l hl
      exact ActualPrimaryCovariance.piece_pressure_inactive l n (hsub hx) θ hl
    · intro l hl
      exact ActualPrimaryCovariance.piece_pressure_inactive l m (hmap hx) θ hl
    · intro l
      exact ActualPrimaryCoherence.piece_pressure_band standardRegion l.2 l.1 n m k hi (x, θ)
  · intro x hx θ i
    apply sum_eq_mul_sum_of_support
    · intro l hl
      exact congrFun (ActualPrimaryCovariance.piece_excluded_inactive l n (hsub hx) θ hl) i
    · intro l hl
      exact congrFun (ActualPrimaryCovariance.piece_excluded_inactive l m (hmap hx) θ hl) i
    · intro l
      exact congrFun (ActualPrimaryCoherence.piece_excluded_band standardRegion l.2 l.1 n m k hi
          (x, θ)) i
  · intro x hx θ i
    simp [seed, CorrectionInitialization.bandSeed]

end ActualSeed

section FinalState

open CorrectionInitialization.ActualPrimary GaugeStateCoherence

theorem primary_primitive (B N0 : ℕ) :
    PrimitiveData standardRegion commonGauge.radial.inner commonGauge.radial.outer
      (commonContext B) (primary B N0) :=
  primary_primitive_of_seed B N0 (seed_primitive B N0)

theorem temporal_primitive (B N0 : ℕ) :
    PrimitiveData standardRegion commonGauge.radial.inner commonGauge.radial.outer
      (commonContext B) (temporal B N0) :=
  temporal_primitive_of_seed B N0 (seed_primitive B N0)

theorem ranked_primitive (B N0 : ℕ) :
    PrimitiveData standardRegion commonGauge.radial.inner commonGauge.radial.outer
      (commonContext B) (ranked B N0) :=
  ranked_primitive_of_seed B N0 (seed_primitive B N0)

theorem initialized_primitive (B N0 : ℕ) :
    PrimitiveData standardRegion commonGauge.radial.inner commonGauge.radial.outer
      (commonContext B) (initialized B N0) :=
  initialized_primitive_of_seed B N0 (seed_primitive B N0)

/-- The two retained aliases are the actual temporal and reconstructed-pressure aliases. -/
theorem initialized_aliases (B N0 : ℕ) :
    (initialized B N0).errors.aliasError =
      VariableGaugeMean.temporalAliasState commonGauge h
          (CorrectionInitialization.CommonWindow.index h)
        (commonContext B) (primary B N0) +
      VariableGaugeMean.pressureAliasState commonGauge (commonContext B) (ranked B N0) :=
  (CorrectionInitialization.GaugeInitialization.initializedBands_error_components commonGauge
      rankData
    h (CorrectionInitialization.CommonWindow.index h) ((0,1),0) (commonContext B)
    (activeLabels standardRegion B N0) (pieces B N0) (baseError B)).2.2

/-- Full radial, angular, and free auxiliary fibers over every common chart region. -/
theorem initialized_band (B N0 n m k : ℕ)
    (hi : CorrectionInitialization.CommonWindow.index h n + k =
        CorrectionInitialization.CommonWindow.index h m)
    {V : Set Plane} (hV : IsOpen V) (hsub : V ⊆ standardRegion.carrier)
    (hmap : MapsTo (bandSlowEquiv h n m) V standardRegion.carrier) :
    StateOn (PhysicalMeanDomain.slowDomain V) (bandChartEquiv h n m k)
      (bandVelocityScale h n m) (bandScale n m) (initialized B N0) (initialized B N0) n m :=
  initialized_band_of_seed B N0 n m k hi hV hsub hmap (seed_primitive B N0)
    (seed_band B N0 n m k hi hsub hmap)

/-- Overlap, given by `standardRegion.carrier ∩ (bandSlowEquiv h n m) ⁻¹'
standardRegion.carrier`. -/
noncomputable def overlap (n m : ℕ) : Set Plane :=
  standardRegion.carrier ∩ (bandSlowEquiv h n m) ⁻¹' standardRegion.carrier

theorem overlap_open (n m : ℕ) : IsOpen (overlap n m) :=
  standardRegion.isOpen.inter (standardRegion.isOpen.preimage (bandSlowEquiv h n m).continuous)

theorem initialized_on_overlap (B N0 n m k : ℕ)
    (hi : CorrectionInitialization.CommonWindow.index h n + k =
        CorrectionInitialization.CommonWindow.index h m) :
    StateOn (PhysicalMeanDomain.slowDomain (overlap n m)) (bandChartEquiv h n m k)
      (bandVelocityScale h n m) (bandScale n m) (initialized B N0) (initialized B N0) n m :=
  initialized_band B N0 n m k hi (overlap_open n m) inter_subset_left (fun _ hx => hx.2)

theorem initialized_alias_band (B N0 n m k : ℕ)
    (hi : CorrectionInitialization.CommonWindow.index h n + k =
        CorrectionInitialization.CommonWindow.index h m)
    {x : Point} (hx : x.2.1 ∈ overlap n m) (θ : ℝ) (i : Fin 3) :
    (initialized B N0).errors.aliasError n (x, θ) i =
      (bandVelocityScale h n m * bandVelocityScale h n m * bandScale n m) *
        (initialized B N0).errors.aliasError m (bandChartEquiv h n m k x, θ) i :=
  (initialized_on_overlap B N0 n m k hi).aliasError x hx θ i

end FinalState

end

end NavierStokes.ActualInitialCoherence

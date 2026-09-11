/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedOutputBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleAssembly
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularCycleData
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleCoherence
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualIterationLedger
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedCommonDynamics
import LeanPool.NavierStokesAndEuler.NavierStokes.MeanStageRegularity
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularMeanGain
public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectionAnalyticStep
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedStageControls
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualInitialExcluded
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualWaveRegularityData
import LeanPool.NavierStokesAndEuler.NavierStokes.UniformBlockBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleParameters
import LeanPool.NavierStokesAndEuler.NavierStokes.SignedCrossDefectClass

/-!
# Preservation by the actual correction cycle

The fixed parameters, current residual, signed request, and comparison
primary are those of the existing initialization. The concrete wave
constructions supply the inputs to the generic analytic step.
-/

section

/-!
# The actual signed mean cross and its physical scale

The fixed comparison primary is the actual tangent block, and every signed
coefficient uses the same selected matrix, pulse and once-applied cutoff.
The physical partition scale is `Q n * q_normalized`; finite low bands retain
their partition factor.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.ActualSignedMeanBinding

open Set Function Filter
open scoped ContDiff Topology BigOperators
open CorrectionInitialization.ActualPrimary ActualPrimaryCovariance

/-- Point: an abbreviation for `LocalSignedRequest.Point`. -/
abbrev Point := LocalSignedRequest.Point
/-- Full point: an abbreviation for `Point × ℝ`. -/
abbrev FullPoint := Point × ℝ
/-- Vec2: an abbreviation for `SignedWaveUpdate.Vec2`. -/
abbrev Vec2 := SignedWaveUpdate.Vec2
/-- Mat2: an abbreviation for `SignedWaveUpdate.Mat2`. -/
abbrev Mat2 := SignedWaveUpdate.Mat2
/-- Space: an abbreviation for `ProblemStatement.Space`. -/
abbrev Space := ProblemStatement.Space
/-- Frequency: an abbreviation for `TorusInverse.Frequency /-! ## The legacy normalized-tail
input cannot describe this chart -/`. -/
abbrev Frequency := TorusInverse.Frequency

/-! ## The legacy normalized-tail input cannot describe this chart -/

theorem Q_le_half {n : ℕ} (hn : 1 ≤ n) : ChartScales.Q n ≤ 1 / 2 := by
  calc
    ChartScales.Q n ≤ (2 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (neg_le_neg (by exact_mod_cast hn : (1 : ℝ) ≤ n))
    _ = 1 / 2 := by norm_num

theorem legacy_nativeData_excludes_strip (B : SignedMeanGain.NativeData
    ActualInitialization.geometry)
    {x : Point} (hx : x ∈ ActualInitialization.geometry.strip.domain) : False := by
  have hs := ActualInitialization.geometry.strip_subset hx
  have hlarge : (1 / 2 : ℝ) < SimilarityCoordinates.coordinateQ (2 * h) x.2.1 := hs.2.1
  have hsmall := (B.tail_bound 0 x hx).trans (Q_le_half (B.index_pos 0))
  exact (not_lt_of_ge hsmall) hlarge

theorem normalized_axis_scale : SimilarityCoordinates.coordinateQ (2 * h) (1, 0) = 1 := by
  symm
  exact SimilarityCoordinates.eq_coordinateQ (by linarith [outgoing.data.h_pos])
    (by linarith [outgoing.data.h_lt_half]) (by norm_num) (by norm_num)
    (by simp [SimilarityCoordinates.forwardScalar])

theorem actual_strip_nonempty : ActualInitialization.geometry.strip.domain.Nonempty := by
  let G := ActualInitialization.geometry
  refine ⟨((G.patch.a + G.patch.b) / 2, ((1, 0), (0, 0))), ?_⟩
  apply (LocalSignedRequest.movingStrip_domain G.region G.patch.a G.patch.b
    G.leftWeight G.rightWeight G.patch.a_pos G.left_pos G.right_pos
    G.epsilon G.slow G.epsilon_pos G.epsilon_le_one G.slow_ge_one _).mpr
  constructor
  · change 0 < (1 : ℝ) ∧ SimilarityCoordinates.coordinateQ (2 * h) (1, 0) ∈ Ioo (1 / 2 : ℝ) 2
    rw [normalized_axis_scale]
    norm_num
  · change ((G.patch.a + G.patch.b) / 2) /
      Real.sqrt (SimilarityCoordinates.coordinateQ (2 * h) (1, 0)) ∈ Ioo G.patch.a G.patch.b
    rw [normalized_axis_scale, Real.sqrt_one, div_one]
    constructor <;> linarith [G.patch.a_lt_b]

theorem no_legacy_nativeData : IsEmpty (SignedMeanGain.NativeData ActualInitialization.geometry) :=
    by
  obtain ⟨x, hx⟩ := actual_strip_nonempty
  exact ⟨fun B => legacy_nativeData_excludes_strip B hx⟩

/-! ## Shared matrix, scaled target and ratio of the signed coefficients -/

variable {B N0 : ℕ}

/-- Velocity scale, given by `PhysicalParticularWave.velocityWeight h (ChartScales.Q n)
(ChartScales.Q (BaseChartJets.cellBand L))`. -/
noncomputable def velocityScale (L : Label B N0) (n : ℕ) : ℝ :=
  PhysicalParticularWave.velocityWeight h (ChartScales.Q n) (ChartScales.Q (BaseChartJets.cellBand
      L))

/-- Common matrix, given by `covariance B N0 L (nativePoint n x L)`. -/
noncomputable def commonMatrix (L : Label B N0) (n : ℕ) (x : Point) : Mat2 :=
  covariance B N0 L (nativePoint n x L)

/-- Reference target, defined pointwise by `PrimaryTargetBounds.actualTarget modulation
(nativePoint n x L) i`. -/
noncomputable def referenceTarget (L : Label B N0) (n : ℕ) (x : Point) : Vec2 :=
  fun i => PrimaryTargetBounds.actualTarget modulation (nativePoint n x L) i

/-- Common target, given by `(ActualSignedStageControls.coefficientScale (L, (0 : Fin 2)) n) ^ 2
• referenceTarget L n x`. -/
noncomputable def commonTarget (L : Label B N0) (n : ℕ) (x : Point) : Vec2 :=
  (ActualSignedStageControls.coefficientScale (L, (0 : Fin 2)) n) ^ 2 • referenceTarget L n x

/-- Signed ratio, constructed using `SignedCovariance.increment`. -/
noncomputable def signedRatio (request : ℕ → FullPoint → Vec2) (L : Label B N0)
    (n : ℕ) (x : Point) (j : Fin 2) : ℝ :=
  SignedCovariance.increment (commonMatrix L n x) (commonTarget L n x) (request n (x, 0)) j /
    SmoothCovariance.amplitudes (commonMatrix L n x) (commonTarget L n x) j

theorem velocityScale_pos (L : Label B N0) (n : ℕ) : 0 < velocityScale L n :=
  PhysicalParticularWave.ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos _) _

theorem velocityScale_eq (L : Label B N0) (n : ℕ) :
    velocityScale L n = ChartScales.Q n ^ CoordinateAlgebra.A h *
      ChartScales.Q (BaseChartJets.cellBand L) ^ (-CoordinateAlgebra.A h) := by
  simp only [velocityScale, PhysicalParticularWave.velocityWeight,
      PhysicalParticularWave.ratioPower,
    Real.rpow_neg (ChartScales.Q_pos _).le, div_eq_mul_inv]

theorem commonMatrix_eq (L : Label B N0) (n : ℕ) (x : Point) (j : Fin 2) (k : Frequency) :
    ActualSignedStageControls.matrix (L, j) k n (x, 0) = commonMatrix L n x := rfl

theorem commonTarget_eq (L : Label B N0) (n : ℕ) (x : Point) (j : Fin 2) (k : Frequency) :
    ActualSignedStageControls.target (L, j) k n (x, 0) = commonTarget L n x := rfl

theorem commonTarget_cone (L : Label B N0) (n : ℕ) {x : Point}
    (hx : x ∈ ActualInitialization.geometry.strip.domain)
    (hm : spatialMask L (nativePoint n x L) ≠ 0) :
    SmoothCovariance.StrictCone (commonMatrix L n x) (commonTarget L n x) := by
  have hT := BaseContextAssembly.nativeStrip_time nominal standardRegion hx
  have hp := spatialMask_carrier L (nativePoint_time n hT L) hm
  have hbase := sourcePair_strictCone L (nativePoint n x L) hp
    (nativePoint_reference n hx L hm) (nativePoint_weight_pos n hx L)
  rw [← PrimaryFieldAssembly.SourcePair.sourceMatrix_eq, sourcePair_matrix] at hbase
  apply (SmoothCovariance.weights_pos_iff _ _).mp
  intro i
  rw [commonTarget, PhysicalSignedWave.weights_smul_target]
  exact mul_pos (sq_pos_of_pos (ActualSignedStageControls.coefficientScale_pos (L, 0) n))
    (hbase.weights_pos i)

theorem primary_scalar_common (L : Label B N0) (n : ℕ) (x : Point) (m : ℝ) (j : Fin 2) :
    PartitionedCovariance.amplitude (ChartScales.epsilon h n) m
      (commonMatrix L n x) (commonTarget L n x) j =
      velocityScale L n * PartitionedCovariance.amplitude
        (ChartScales.epsilon h (BaseChartJets.cellBand L)) m
        (commonMatrix L n x) (referenceTarget L n x) j :=
  PhysicalSignedWave.primary_scalar_scale _ _ m (ChartScales.epsilon_pos h n)
    (ChartScales.epsilon_pos h _) (velocityScale_pos L n) j

theorem signed_scalar_ratio (request : ℕ → FullPoint → Vec2) (L : Label B N0) (n : ℕ)
    {x : Point} (hx : x ∈ ActualInitialization.geometry.strip.domain) (j : Fin 2) :
    Real.sqrt (ChartScales.epsilon h n) *
      SignedCovariance.increment (commonMatrix L n x) (commonTarget L n x) (request n (x, 0)) j *
        spatialMask L (nativePoint n x L) =
      signedRatio request L n x j * velocityScale L n *
        PartitionedCovariance.amplitude (ChartScales.epsilon h (BaseChartJets.cellBand L))
          (spatialMask L (nativePoint n x L)) (commonMatrix L n x) (referenceTarget L n x) j := by
  by_cases hm : spatialMask L (nativePoint n x L) = 0
  · simp [hm, PartitionedCovariance.amplitude]
  have ha := (commonTarget_cone L n hx hm).amplitudes_pos j
  rw [mul_assoc (signedRatio request L n x j), ← primary_scalar_common]
  unfold signedRatio PartitionedCovariance.amplitude
  field_simp

/-! ## The actual once-cutoff coefficients -/

theorem localized_amplitude_ratio (request : ℕ → FullPoint → Vec2) (L : Label B N0)
    (n : ℕ) {x : Point} (hx : x ∈ ActualInitialization.geometry.strip.domain)
    (j : Fin 2) (k : Frequency) :
    (((ActualSignedStageControls.parameters (L, j)).copyData ActualInitialization.geometry.strip
        request).localized k).amplitude
      n (x, 0) =
      signedRatio request L n x j • (velocityScale L n •
        CurlClassBounds.complexify (cutVelocity j L
          (nativePoint n x L, (geometry j L).coordinates k (toAbsolute n x).2))) := by
  have hr := signed_scalar_ratio request L n hx j
  change (ActualSignedStageControls.cutoff (L, j) k n (x, 0)) •
    CurlClassBounds.complexify
      ((Real.sqrt (ChartScales.epsilon h n) *
        SignedCovariance.increment (commonMatrix L n x) (commonTarget L n x) (request n (x, 0)) j *
        spatialMask L (nativePoint n x L)) •
      ActualSignedStageControls.fundamental (L, j) k n (x, 0)) = _
  rw [hr]
  simp only [ActualSignedStageControls.cutoff, ActualSignedStageControls.fundamental,
    ActualSignedStageControls.nativePoint, cutVelocity, rawVelocity,
        PartitionedCovariance.amplitude,
    map_smul, smul_smul]
  congr 1
  simp only [commonMatrix, nativePoint]
  rw [show referenceTarget L n x = (fun i => PrimaryTargetBounds.actualTarget modulation
    (nativeSlow L (toAbsolute n x)) i) from rfl]
  ring

theorem signed_common_amplitude_ratio (request : ℕ → FullPoint → Vec2) (L : Label B N0)
    (n : ℕ) {x : Point} (hx : x ∈ ActualInitialization.geometry.strip.domain) (j : Fin 2) :
    ((ActualSignedStageControls.parameters (L, j)).copyData ActualInitialization.geometry.strip
        request).common.amplitude
      n (x, 0) = signedRatio request L n x j • cutAmplitude j L n (x, 0) := by
  rw [cutAmplitude_eq_common j L n hx 0, ← velocityScale_eq]
  change (∑' k : Frequency,
    (((ActualSignedStageControls.parameters (L, j)).copyData ActualInitialization.geometry.strip
        request).localized k).amplitude
      n (x, 0)) = _
  unfold commonAmplitude
  rw [← tsum_const_smul'', ← tsum_const_smul'']
  exact tsum_congr (fun k => localized_amplitude_ratio request L n hx j k)

theorem primaryBlock_eq_model (L : Label B N0) (j : Fin 2) :
    ActualInitialization.tangentBlock (L, j) = SignedWaveUpdate.blockOfCoefficients
      ((chartCoefficients j L).withCutoff (chartCutoff j L))
      (fun _ => PrimaryGeometryAssembly.angularMode certificate modulation (choice B N0).prepared j
          L) := rfl

theorem primary_tangent_band (l : Label B N0 × Fin 2) :
    (ActualInitialization.tangentBlock l).BandLimited 1 :=
  CorrectionInitialization.PrimaryHarmonics.block_band _ _ _

theorem actual_sameCarrier (request : ℕ → FullPoint → Vec2) (L : Label B N0) (j : Fin 2) :
    LabelSumBounds.SameCarrier (ActualInitialization.tangentBlock (L, j))
      ((ActualSignedStageControls.parameters (L, j)).tangentBlock
          ActualInitialization.geometry.strip request) :=
  ⟨rfl, rfl, rfl⟩

theorem signed_tangent_ratio (request : ℕ → FullPoint → Vec2) (L : Label B N0)
    (n : ℕ) {x : Point} (hx : x ∈ ActualInitialization.geometry.strip.domain)
    (j : Fin 2) (theta : ℝ) (i : Fin 3) :
    ((ActualSignedStageControls.parameters (L, j)).tangentBlock ActualInitialization.geometry.strip
        request).oscillation
      n (x, theta) i = signedRatio request L n x j *
      (ActualInitialization.tangentBlock (L, j)).oscillation n (x, theta) i := by
  rw [primaryBlock_eq_model]
  unfold CorrectionStep.PeriodizedSignedParameters.tangentBlock SignedWaveUpdate.blockOfCoefficients
  rw [SignedWaveUpdate.coefficientBlock_velocity, SignedWaveUpdate.coefficientBlock_velocity,
    signed_common_amplitude_ratio request L n hx j]
  simp only [PeriodizedWaveBounds.CopyData.common,
      CorrectionStep.PeriodizedSignedParameters.copyData,
    ActualSignedStageControls.parameters, LinearWaveBounds.WaveCoefficients.withCutoff,
    cutAmplitude, Pi.smul_apply, Complex.real_smul,
    ← mul_assoc, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, add_zero, sub_zero]
  ring

theorem signedRatio_fiber (c : CorrectionState.Context Point) (u : CorrectionState.State Point)
    (L : Label B N0) (n : ℕ) (x : Point) (Y : TorusInverse.Plane) (j : Fin 2) :
    signedRatio (LocalSignedRequest.fullRequest ActualInitialization.geometry.strip
      ActualInitialization.geometry.patch ActualInitialization.geometry.coord c u)
      L n (x.1, (x.2.1, Y)) j =
    signedRatio (LocalSignedRequest.fullRequest ActualInitialization.geometry.strip
      ActualInitialization.geometry.patch ActualInitialization.geometry.coord c u) L n x j := rfl

/-! ## Individual primary modes at the actual common cover -/

theorem primary_mode_view (n : ℕ) {x : Point}
    (hx : x ∈ ActualInitialization.geometry.strip.domain)
    (l : Label B N0 × Fin 2) (Y : TorusInverse.Plane) (theta : ℝ) (i : Fin 3) :
    (ActualInitialization.tangentBlock l).oscillation n ((x.1, (x.2.1, Y)), theta) i =
      ChartScales.Q n ^ CoordinateAlgebra.A h * viewTangent n x l Y theta i := by
  rw [ActualInitialization.tangentBlock_represents]
  have hr := ((BaseContextAssembly.nativeStrip_mem nominal standardRegion x).mp hx).2
  have hT := BaseContextAssembly.nativeStrip_time nominal standardRegion hx
  have hR := BaseContextAssembly.nativeStrip_radius nominal standardRegion hx
  have hrad : PrimaryTargetBounds.profileRadius h (nativePoint n x l.1) ∈
      Ioo (PrimaryTargetBounds.leftRadius nominal) (PrimaryTargetBounds.rightRadius nominal) := by
    rwa [nativePoint_profileRadius n hT hR]
  unfold ActualInitialization.primaryPiece
  rw [piece_tangent_representation,
    absoluteTangent_eq l.2 l.1 (toAbsolute n (x.1, (x.2.1, Y)), theta) hrad]
  rfl

theorem primary_cross_zero (n : ℕ) {x : Point}
    (hx : x ∈ ActualInitialization.geometry.strip.domain)
    {l m : Label B N0 × Fin 2} (hlm : l ≠ m)
    (Y : TorusInverse.Plane) (theta : ℝ) (i : Fin 2) :
    (ActualInitialization.tangentBlock l).oscillation n ((x.1, (x.2.1, Y)), theta) 0 *
      (ActualInitialization.tangentBlock m).oscillation n ((x.1, (x.2.1, Y)), theta) i.succ = 0 :=
          by
  rw [primary_mode_view n hx, primary_mode_view n hx]
  have hz := viewTangent_cross_zero n hx hlm Y theta i
  calc
    _ = (ChartScales.Q n ^ CoordinateAlgebra.A h) ^ 2 *
      (viewTangent n x l Y theta 0 * viewTangent n x m Y theta i.succ) := by ring
    _ = 0 := by rw [hz, mul_zero]

theorem primary_diagonal_continuous (n : ℕ) {x : Point}
    (hx : x ∈ ActualInitialization.geometry.strip.domain)
    (l : Label B N0 × Fin 2) (hl : l ∈ activeLabels standardRegion B N0 n) (i : Fin 2) :
    (∀ Y, Continuous (fun theta =>
      (ActualInitialization.tangentBlock l).oscillation n ((x.1, (x.2.1, Y)), theta) 0 *
      (ActualInitialization.tangentBlock l).oscillation n ((x.1, (x.2.1, Y)), theta) i.succ)) ∧
    Continuous (fun Y => SmoothLoop.angularMean (fun theta =>
      (ActualInitialization.tangentBlock l).oscillation n ((x.1, (x.2.1, Y)), theta) 0 *
      (ActualInitialization.tangentBlock l).oscillation n ((x.1, (x.2.1, Y)), theta) i.succ)) := by
  have hc := viewTangent_diagonal_continuous n hx l hl i
  have he (Y : TorusInverse.Plane) (theta : ℝ) :
      (ActualInitialization.tangentBlock l).oscillation n ((x.1, (x.2.1, Y)), theta) 0 *
      (ActualInitialization.tangentBlock l).oscillation n ((x.1, (x.2.1, Y)), theta) i.succ =
      (ChartScales.Q n ^ CoordinateAlgebra.A h) ^ 2 *
        (viewTangent n x l Y theta 0 * viewTangent n x l Y theta i.succ) := by
    rw [primary_mode_view n hx, primary_mode_view n hx]
    ring
  simp_rw [he]
  constructor
  · intro Y
    exact continuous_const.mul (hc.1 Y)
  · simp_rw [SmoothLoop.angularMean_const_mul]
    exact continuous_const.mul hc.2

theorem primary_diagonal_average (n : ℕ) {x : Point}
    (hx : x ∈ ActualInitialization.geometry.strip.domain)
    (L : Label B N0) (hL : L ∈ unsignedLabels B N0 n) (j i : Fin 2) :
    PartitionedCovariance.doubleAverage (fun Y theta =>
      (ActualInitialization.tangentBlock (L, j)).oscillation n ((x.1, (x.2.1, Y)), theta) 0 *
      (ActualInitialization.tangentBlock (L, j)).oscillation n ((x.1, (x.2.1, Y)), theta) i.succ) =
      (PartitionedCovariance.amplitude (ChartScales.epsilon h n)
        (spatialMask L (nativePoint n x L)) (commonMatrix L n x) (commonTarget L n x) j) ^ 2 *
        commonMatrix L n x i j := by
  by_cases hm : spatialMask L (nativePoint n x L) = 0
  · simp only [primary_mode_view n hx, viewTangent, physicalTangentMode_zero_of_mask j L _ hm,
      Pi.zero_apply, mul_zero, PartitionedCovariance.doubleAverage, SmoothLoop.angularMean,
      TorusAverages.squareAverage, intervalIntegral.integral_zero, zero_div,
      PartitionedCovariance.amplitude, hm, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul]
  have hT := BaseContextAssembly.nativeStrip_time nominal standardRegion hx
  have hp := spatialMask_carrier L (nativePoint_time n hT L) hm
  let P := (sourcePair L (nativePoint n x L) hp).pairData
  have hmat : P.matrix = commonMatrix L n x := by
    rw [← PrimaryFieldAssembly.SourcePair.sourceMatrix_eq, sourcePair_matrix]
    rfl
  have he (Y : TorusInverse.Plane) (theta : ℝ) :
      (ActualInitialization.tangentBlock (L, j)).oscillation n ((x.1, (x.2.1, Y)), theta) 0 *
      (ActualInitialization.tangentBlock (L, j)).oscillation n ((x.1, (x.2.1, Y)), theta) i.succ =
      (ChartScales.Q n ^ CoordinateAlgebra.A h) ^ 2 *
        (viewTangent n x (L, j) Y theta 0 * viewTangent n x (L, j) Y theta i.succ) := by
    rw [primary_mode_view n hx, primary_mode_view n hx]
    ring
  simp_rw [he]
  rw [PartitionedCovariance.doubleAverage_const_mul]
  simp only [viewTangent, physicalTangentMode_eq_slot j L _ hp]
  rw [pair_diagonal_common P vectors_det (active_cover_le n hL), hmat]
  rw [primary_scalar_common, velocityScale_eq]
  change _ = (_ * PartitionedCovariance.amplitude _ _ _ _ j) ^ 2 * _
  simp only [PartitionedCovariance.amplitude, commonMatrix, spatialMask]
  rw [show referenceTarget L n x = (fun i => PrimaryTargetBounds.actualTarget modulation
    (nativePoint n x L) i) from rfl]
  ring

/-! ## The literal requested field and its finite covariance sum -/

/-- Actual request, constructed using `LocalSignedRequest.fullRequest`. -/
noncomputable def actualRequest (c : CorrectionState.Context Point)
    (u : CorrectionState.State Point) : ℕ → FullPoint → Vec2 :=
  LocalSignedRequest.fullRequest ActualInitialization.geometry.strip
    ActualInitialization.geometry.patch ActualInitialization.geometry.coord c u

/-- Actual signed block, given by `(ActualSignedStageControls.parameters l).tangentBlock
ActualInitialization.geometry.strip (actualRequest c u)`. -/
noncomputable def actualSignedBlock (c : CorrectionState.Context Point)
    (u : CorrectionState.State Point) (l : Label B N0 × Fin 2) :=
  (ActualSignedStageControls.parameters l).tangentBlock ActualInitialization.geometry.strip
    (actualRequest c u)

/-- Actual primary field, given by `LabelSumBounds.fieldSum (activeLabels standardRegion B N0)
(fun l => (ActualInitialization.tangentBlock l).oscillation)`. -/
noncomputable def actualPrimaryField (B N0 : ℕ) : CorrectionState.Oscillation Point :=
  LabelSumBounds.fieldSum (activeLabels standardRegion B N0)
    (fun l => (ActualInitialization.tangentBlock l).oscillation)

/-- Actual signed field, given by `LabelSumBounds.fieldSum (activeLabels standardRegion B N0)
(fun l => (actualSignedBlock c u l).oscillation)`. -/
noncomputable def actualSignedField (B N0 : ℕ) (c : CorrectionState.Context Point)
    (u : CorrectionState.State Point) : CorrectionState.Oscillation Point :=
  LabelSumBounds.fieldSum (activeLabels standardRegion B N0)
    (fun l => (actualSignedBlock c u l).oscillation)

/-- Actual cross, given by `LabelSumBounds.symmetricCovariance (actualPrimaryField B N0)
(actualSignedField B N0 c u)`. -/
noncomputable def actualCross (B N0 : ℕ) (c : CorrectionState.Context Point)
    (u : CorrectionState.State Point) : LabelSumBounds.Tensor Point :=
  LabelSumBounds.symmetricCovariance (actualPrimaryField B N0) (actualSignedField B N0 c u)

theorem actualSignedBlock_fiber (c : CorrectionState.Context Point)
    (u : CorrectionState.State Point) (l : Label B N0 × Fin 2)
    (n : ℕ) {x : Point} (hx : x ∈ ActualInitialization.geometry.strip.domain)
    (Y : TorusInverse.Plane) (theta : ℝ) (i : Fin 3) :
    (actualSignedBlock c u l).oscillation n ((x.1, (x.2.1, Y)), theta) i =
      signedRatio (actualRequest c u) l.1 n x l.2 *
        (ActualInitialization.tangentBlock l).oscillation n ((x.1, (x.2.1, Y)), theta) i := by
  rw [actualSignedBlock, signed_tangent_ratio (actualRequest c u) l.1 n
    (SignedMeanGain.Geometry.strip_fiber ActualInitialization.geometry hx Y)]
  rfl

theorem actual_cross_diagonal (c : CorrectionState.Context Point)
    (u : CorrectionState.State Point) (n : ℕ) {x : Point}
    (hx : x ∈ ActualInitialization.geometry.strip.domain)
    (Y : TorusInverse.Plane) (theta : ℝ) (i : Fin 2) :
    actualPrimaryField B N0 n ((x.1, (x.2.1, Y)), theta) 0 *
        actualSignedField B N0 c u n ((x.1, (x.2.1, Y)), theta) i.succ +
      actualSignedField B N0 c u n ((x.1, (x.2.1, Y)), theta) 0 *
        actualPrimaryField B N0 n ((x.1, (x.2.1, Y)), theta) i.succ =
    ∑ l ∈ activeLabels standardRegion B N0 n,
      (2 * signedRatio (actualRequest c u) l.1 n x l.2) *
        ((ActualInitialization.tangentBlock l).oscillation n ((x.1, (x.2.1, Y)), theta) 0 *
         (ActualInitialization.tangentBlock l).oscillation n ((x.1, (x.2.1, Y)), theta) i.succ) :=
             by
  classical
  simp only [actualPrimaryField, actualSignedField, LabelSumBounds.fieldSum,
    actualSignedBlock_fiber c u _ n hx]
  rw [PartitionedCovariance.sum_product_diagonal,
    PartitionedCovariance.sum_product_diagonal, ← Finset.sum_add_distrib]
  · apply Finset.sum_congr rfl
    intro l hl
    ring
  · intro l hl m hm hlm
    rw [mul_assoc, primary_cross_zero n hx hlm, mul_zero]
  · intro l hl m hm hlm
    rw [mul_left_comm, primary_cross_zero n hx hlm, mul_zero]

theorem actual_cross_average_sum (c : CorrectionState.Context Point)
    (u : CorrectionState.State Point) (n : ℕ) {x : Point}
    (hx : x ∈ ActualInitialization.geometry.strip.domain) (i : Fin 2) :
    StateMomentBalances.meanBar (actualCross B N0 c u 0 i.succ) n x =
      ∑ l ∈ activeLabels standardRegion B N0 n,
        (2 * signedRatio (actualRequest c u) l.1 n x l.2) *
          ((PartitionedCovariance.amplitude (ChartScales.epsilon h n)
            (spatialMask l.1 (nativePoint n x l.1))
            (commonMatrix l.1 n x) (commonTarget l.1 n x) l.2) ^ 2 *
            commonMatrix l.1 n x i l.2) := by
  rw [actualCross, SignedMeanGain.meanBar_symmetricCovariance
    (actualPrimaryField B N0) (actualSignedField B N0 c u)
    (LabelSumBounds.fieldSum_angularContinuous _ _
      (fun _ => LabelSumBounds.block_angularContinuous _))
    (LabelSumBounds.fieldSum_angularContinuous _ _
      (fun _ => LabelSumBounds.block_angularContinuous _))]
  simp_rw [actual_cross_diagonal c u n hx]
  rw [PartitionedCovariance.doubleAverage_sum]
  · apply Finset.sum_congr rfl
    intro l hl
    rw [PartitionedCovariance.doubleAverage_const_mul, primary_diagonal_average n hx]
    rw [activeLabels_product] at hl
    exact (Finset.mem_product.mp hl).1
  · intro l hl Y
    exact continuous_const.mul ((primary_diagonal_continuous n hx l hl i).1 Y)
  · intro l hl
    simp_rw [SmoothLoop.angularMean_const_mul]
    exact continuous_const.mul (primary_diagonal_continuous n hx l hl i).2

theorem pair_signed_reconstruction (request : ℕ → FullPoint → Vec2)
    (L : Label B N0) (n : ℕ) {x : Point}
    (hx : x ∈ ActualInitialization.geometry.strip.domain) (i : Fin 2) :
    ∑ j : Fin 2,
      (2 * signedRatio request L n x j) *
        ((PartitionedCovariance.amplitude (ChartScales.epsilon h n)
          (spatialMask L (nativePoint n x L)) (commonMatrix L n x) (commonTarget L n x) j) ^ 2 *
          commonMatrix L n x i j) =
      ChartScales.epsilon h n * spatialMask L (nativePoint n x L) ^ 2 * request n (x, 0) i := by
  by_cases hm : spatialMask L (nativePoint n x L) = 0
  · simp [PartitionedCovariance.amplitude, hm]
  have hcone := commonTarget_cone L n hx hm
  have hrec := SignedCovariance.cross_reconstruct_component
    (commonMatrix L n x) (commonTarget L n x) (request n (x, 0)) hcone i
  have heps := Real.sq_sqrt (ChartScales.epsilon_pos h n).le
  calc
    _ = ChartScales.epsilon h n * spatialMask L (nativePoint n x L) ^ 2 *
        (2 * ((commonMatrix L n x).mulVec (fun j =>
          SmoothCovariance.amplitudes (commonMatrix L n x) (commonTarget L n x) j *
            SignedCovariance.increment (commonMatrix L n x) (commonTarget L n x)
              (request n (x, 0)) j)) i) := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have ha := ne_of_gt (hcone.amplitudes_pos j)
      unfold signedRatio PartitionedCovariance.amplitude
      simp only [mul_pow, heps]
      field_simp
    _ = _ := by rw [hrec]

/-! ## Exact physical partition factor, and exact cancellation on its tail -/

theorem requested_cross_factor (B N0 : ℕ) (c : CorrectionState.Context Point)
    (u : CorrectionState.State Point) (n : ℕ) {x : Point}
    (hx : x ∈ ActualInitialization.geometry.strip.domain) (i : Fin 2) :
    StateMomentBalances.meanBar (actualCross B N0 c u 0 i.succ) n x =
      partitionFactor B N0 n x * LocalSignedRequest.requestedStress
        ActualInitialization.geometry.patch ActualInitialization.geometry.coord c u n x i := by
  rw [actual_cross_average_sum c u n hx i, activeLabels_product,
    Finset.product_eq_sprod, Finset.sum_product]
  simp_rw [pair_signed_reconstruction (actualRequest c u) _ n hx i]
  have he : ChartScales.epsilon h n * actualRequest c u n (x, 0) i =
      LocalSignedRequest.requestedStress ActualInitialization.geometry.patch
        ActualInitialization.geometry.coord c u n x i := by
    change ChartScales.epsilon h n * ((ChartScales.epsilon h n)⁻¹ * _) = _
    rw [← mul_assoc, mul_inv_cancel₀ (ChartScales.epsilon_pos h n).ne', one_mul]
  rw [partitionFactor, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro L hL
  rw [mul_right_comm, he, mul_comm]

/-- The physical scale, and therefore this threshold, is shared by every
signed request made from the fixed primary choice. -/
theorem requested_cross_tail (B N0 : ℕ) (c : CorrectionState.Context Point)
    (u : CorrectionState.State Point) {n : ℕ}
    (hn : (choice B N0).prepared.N + 1 ≤ n) {x : Point}
    (hx : x ∈ ActualInitialization.geometry.strip.domain) (i : Fin 2) :
    StateMomentBalances.meanBar (actualCross B N0 c u 0 i.succ) n x =
      LocalSignedRequest.requestedStress ActualInitialization.geometry.patch
        ActualInitialization.geometry.coord c u n x i := by
  rw [requested_cross_factor B N0 c u n hx i,
    partitionFactor_eq_one B N0 n hx (physicalScale_tail B N0 hn hx), one_mul]

/-- Earlier bands retain their actual cutoff deficit.  In particular this
theorem makes no assertion of cancellation on every normalized band. -/
theorem requested_cross_defect (B N0 : ℕ) (c : CorrectionState.Context Point)
    (u : CorrectionState.State Point) (n : ℕ) {x : Point}
    (hx : x ∈ ActualInitialization.geometry.strip.domain) (i : Fin 2) :
    StateMomentBalances.meanBar (actualCross B N0 c u 0 i.succ) n x -
      LocalSignedRequest.requestedStress ActualInitialization.geometry.patch
        ActualInitialization.geometry.coord c u n x i =
      -missingWeight (choice B N0).prepared.N (physicalScale n x) *
        LocalSignedRequest.requestedStress ActualInitialization.geometry.patch
          ActualInitialization.geometry.coord c u n x i := by
  rw [requested_cross_factor B N0 c u n hx i, partitionFactor_eq_one_sub_missing B N0 n hx]
  ring

theorem theta_cross_tail (B N0 : ℕ) (c : CorrectionState.Context Point)
    (u : CorrectionState.State Point) {n : ℕ}
    (hn : (choice B N0).prepared.N + 1 ≤ n) {x : Point}
    (hx : x ∈ ActualInitialization.geometry.strip.domain) :
    StateMomentBalances.meanBar (actualCross B N0 c u 0 1) n x =
      SignedMeanGain.physicalSigma ActualInitialization.geometry 2 (u.thetaResidual c) n x :=
  requested_cross_tail B N0 c u hn hx 0

theorem axial_cross_tail (B N0 : ℕ) (c : CorrectionState.Context Point)
    (u : CorrectionState.State Point) {n : ℕ}
    (hn : (choice B N0).prepared.N + 1 ≤ n) {x : Point}
    (hx : x ∈ ActualInitialization.geometry.strip.domain) :
    StateMomentBalances.meanBar (actualCross B N0 c u 0 2) n x =
      SignedMeanGain.physicalSigma ActualInitialization.geometry 1 (u.axialResidual c) n x :=
  requested_cross_tail B N0 c u hn hx 1

theorem requested_cross_tail_jets (B N0 : ℕ) (c : CorrectionState.Context Point)
    (u : CorrectionState.State Point) {n : ℕ}
    (hn : (choice B N0).prepared.N + 1 ≤ n) {x : Point}
    (hx : x ∈ ActualInitialization.geometry.strip.domain) (i : Fin 2) (m : ℕ) :
    iteratedFDeriv ℝ m (StateMomentBalances.meanBar (actualCross B N0 c u 0 i.succ) n) x =
      iteratedFDeriv ℝ m (fun x => LocalSignedRequest.requestedStress
        ActualInitialization.geometry.patch ActualInitialization.geometry.coord c u n x i) x := by
  exact (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
    (eventually_of_mem (ActualInitialization.geometry.strip.isOpen_domain.mem_nhds hx)
      (fun y hy => requested_cross_tail B N0 c u hn hy i)) m).self_of_nhds

/-! ## Binding to the signed family of the literal correction cycle -/

open CorrectionStep CorrectionState

/-- This is the actual cycle constructor with its particular solver left
as a parameter.  Both fixed and state-dependent actual particular solvers
use this very signed subsystem. -/
noncomputable def cycleParameters
    (particular : (Label B N0 × Fin 2) → ParticularParameters CycleSlow) :
    CycleParameters (Label B N0 × Fin 2) :=
  CycleParameters.ofGeometry ActualInitialization.geometry h
    (CorrectionInitialization.CommonWindow.index h) ActualInitialization.axial
    particular ActualSignedStageControls.parameters rankData

theorem cycle_signedRequest_eq
    (particular : (Label B N0 × Fin 2) → ParticularParameters CycleSlow)
    (v : CycleCoefficients (Label B N0 × Fin 2)) (c : Context Point) (u : State Point) :
    (cycleParameters particular).signedRequest v c u =
      actualRequest c ((cycleParameters particular).afterParticular v c u) := rfl

theorem cycle_signedTangent_eq
    (particular : (Label B N0 × Fin 2) → ParticularParameters CycleSlow)
    (v : CycleCoefficients (Label B N0 × Fin 2)) (c : Context Point) (u : State Point)
    (l : Label B N0 × Fin 2) :
    (cycleParameters particular).signedTangent v c u l =
      actualSignedBlock c ((cycleParameters particular).afterParticular v c u) l := rfl

theorem cycle_signed_sameCarrier
    (particular : (Label B N0 × Fin 2) → ParticularParameters CycleSlow)
    (v : CycleCoefficients (Label B N0 × Fin 2)) (c : Context Point) (u : State Point)
    (l : Label B N0 × Fin 2) :
    LabelSumBounds.SameCarrier (ActualInitialization.tangentBlock l)
      ((cycleParameters particular).signedBlock v c u l) := ⟨rfl, rfl, rfl⟩

theorem cycle_current_signedCarrier
    (particular : (Label B N0 × Fin 2) → ParticularParameters CycleSlow)
    (v : CycleCoefficients (Label B N0 × Fin 2)) (c : Context Point) (u : State Point)
    (hcp : ∀ l, LabelSumBounds.SameCarrier (v.blocks l) (ActualInitialization.tangentBlock l))
    (l : Label B N0 × Fin 2) :
    LabelSumBounds.SameCarrier (v.blocks l) ((cycleParameters particular).signedBlock v c u l) :=
  ⟨(hcp l).frequency, (hcp l).phase, (hcp l).angular⟩

theorem fixedParameters_eq_cycle (B N0 : ℕ) :
    ActualCycleParameters.fixedParameters B N0 =
      cycleParameters (fun l : Label B N0 × Fin 2 =>
        ActualParticularStageControls.canonicalParameters (l.2, l.1)) := rfl

theorem parameters_eq_cycle (x : CycleState (Label B N0 × Fin 2)) :
    ActualCycleParameters.parameters x =
      cycleParameters (fun l => ActualParticularStageControls.parameters
        (ActualCycleParameters.particularState x) (ActualCycleParameters.swap B N0 l)) := rfl

theorem initial_labels (B N0 : ℕ) :
    (ActualInitialization.coefficients B N0).labels = activeLabels standardRegion B N0 := rfl

theorem next_labels
    (p : CycleParameters (Label B N0 × Fin 2))
    (v : CycleCoefficients (Label B N0 × Fin 2)) (c : Context Point) (u : State Point) :
    (p.nextCoefficients v c u).labels = v.labels := rfl

/-! The cycle field identity is stated without expanding its quantitative
`SignedFamily` proof object.  Its coefficient projections are all that the
covariance uses. -/

theorem cycle_cross_eq
    (particular : (Label B N0 × Fin 2) → ParticularParameters CycleSlow)
    (v : CycleCoefficients (Label B N0 × Fin 2)) (c : Context Point) (u : State Point)
    (hlabels : v.labels = activeLabels standardRegion B N0) :
    LabelSumBounds.symmetricCovariance
      (LabelSumBounds.fieldSum v.labels (fun l => (ActualInitialization.tangentBlock
          l).oscillation))
      (LabelSumBounds.fieldSum v.labels
        (fun l => ((cycleParameters particular).signedTangent v c u l).oscillation)) =
      actualCross B N0 c ((cycleParameters particular).afterParticular v c u) := by
  rw [hlabels]
  rfl

theorem cycle_requested_cross_tail
    (particular : (Label B N0 × Fin 2) → ParticularParameters CycleSlow)
    (v : CycleCoefficients (Label B N0 × Fin 2)) (c : Context Point) (u : State Point)
    (hlabels : v.labels = activeLabels standardRegion B N0) {n : ℕ}
    (hn : (choice B N0).prepared.N + 1 ≤ n) {x : Point}
    (hx : x ∈ ActualInitialization.geometry.strip.domain) (i : Fin 2) :
    StateMomentBalances.meanBar (LabelSumBounds.symmetricCovariance
      (LabelSumBounds.fieldSum v.labels (fun l => (ActualInitialization.tangentBlock
          l).oscillation))
      (LabelSumBounds.fieldSum v.labels
        (fun l => ((cycleParameters particular).signedTangent v c u l).oscillation)) 0 i.succ) n x =
      LocalSignedRequest.requestedStress ActualInitialization.geometry.patch
        ActualInitialization.geometry.coord c ((cycleParameters particular).afterParticular v c u)
            n x i := by
  rw [cycle_cross_eq particular v c u hlabels]
  exact requested_cross_tail B N0 c _ hn hx i

theorem fixed_requested_cross_tail
    (v : CycleCoefficients (Label B N0 × Fin 2)) (c : Context Point) (u : State Point)
    (hlabels : v.labels = activeLabels standardRegion B N0) {n : ℕ}
    (hn : (choice B N0).prepared.N + 1 ≤ n) {x : Point}
    (hx : x ∈ ActualInitialization.geometry.strip.domain) (i : Fin 2) :
    StateMomentBalances.meanBar (LabelSumBounds.symmetricCovariance
      (LabelSumBounds.fieldSum v.labels (fun l => (ActualInitialization.tangentBlock
          l).oscillation))
      (LabelSumBounds.fieldSum v.labels
        (fun l => ((ActualCycleParameters.fixedParameters B N0).signedTangent v c u l).oscillation))
          0 i.succ) n x =
      LocalSignedRequest.requestedStress ActualInitialization.geometry.patch
        ActualInitialization.geometry.coord c
          ((ActualCycleParameters.fixedParameters B N0).afterParticular v c u) n x i := by
  rw [fixedParameters_eq_cycle]
  exact cycle_requested_cross_tail _ v c u hlabels hn hx i

theorem literal_requested_cross_tail (state : CycleState (Label B N0 × Fin 2))
    (hlabels : state.coefficients.labels = activeLabels standardRegion B N0) {n : ℕ}
    (hn : (choice B N0).prepared.N + 1 ≤ n) {x : Point}
    (hx : x ∈ ActualInitialization.geometry.strip.domain) (i : Fin 2) :
    StateMomentBalances.meanBar (LabelSumBounds.symmetricCovariance
      (LabelSumBounds.fieldSum state.coefficients.labels
        (fun l => (ActualInitialization.tangentBlock l).oscillation))
      (LabelSumBounds.fieldSum state.coefficients.labels
        (fun l => ((ActualCycleParameters.parameters state).signedTangent
          state.coefficients (commonContext B) state.state l).oscillation)) 0 i.succ) n x =
      LocalSignedRequest.requestedStress ActualInitialization.geometry.patch
        ActualInitialization.geometry.coord (commonContext B)
          ((ActualCycleParameters.parameters state).afterParticular
            state.coefficients (commonContext B) state.state) n x i := by
  rw [parameters_eq_cycle]
  exact cycle_requested_cross_tail _ state.coefficients (commonContext B) state.state hlabels hn hx
      i

section Family

variable {P : (Label B N0 × Fin 2) → ℕ → Point → ℝ} {α δ β η : ℝ}

/-- Only stored coefficient projections identify the quantitative family.
For the literal `CycleParameters.signedFamily`, these equalities are `rfl`. -/
theorem family_cross_eq (c : Context Point) (u : State Point)
    (f : LabelSumBounds.SignedFamily ActualInitialization.geometry.strip P α δ β η)
    (a : SignedMeanGain.Assembly f)
    (hprimary : f.primary = ActualInitialization.tangentBlock)
    (htangent : f.tangent = actualSignedBlock c u)
    (hlabels : a.labels = activeLabels standardRegion B N0) :
    SignedMeanGain.crossTensor f a = actualCross B N0 c u := by
  simp only [SignedMeanGain.crossTensor, SignedMeanGain.primaryField,
    SignedMeanGain.tangentField, hprimary, htangent, hlabels]
  rfl

theorem family_requested_cross_tail (c : Context Point) (u : State Point)
    (f : LabelSumBounds.SignedFamily ActualInitialization.geometry.strip P α δ β η)
    (a : SignedMeanGain.Assembly f)
    (hprimary : f.primary = ActualInitialization.tangentBlock)
    (htangent : f.tangent = actualSignedBlock c u)
    (hlabels : a.labels = activeLabels standardRegion B N0) {n : ℕ}
    (hn : (choice B N0).prepared.N + 1 ≤ n) {x : Point}
    (hx : x ∈ ActualInitialization.geometry.strip.domain) (i : Fin 2) :
    StateMomentBalances.meanBar (SignedMeanGain.crossTensor f a 0 i.succ) n x =
      LocalSignedRequest.requestedStress ActualInitialization.geometry.patch
        ActualInitialization.geometry.coord c u n x i := by
  rw [family_cross_eq c u f a hprimary htangent hlabels]
  exact requested_cross_tail B N0 c u hn hx i

/-- Every requested exponent follows for the literal finite-head defects.
The analytic inputs are the usual supported residual/coefficient estimates,
not an assumption on the cross defect or its vanishing. -/
theorem family_defects_all_exponents (c : Context Point) (u : State Point) {σ κ : ℝ}
    (f : LabelSumBounds.SignedFamily ActualInitialization.geometry.strip P (1 / 2) (17 / 25)
      (1 / 2 + σ - κ) (1 + σ - 2 * κ)) (a : SignedMeanGain.Assembly f)
    (hprimary : f.primary = ActualInitialization.tangentBlock)
    (htangent : f.tangent = actualSignedBlock c u)
    (hlabels : a.labels = activeLabels standardRegion B N0)
    (hS : ∀ i j, SignedMeanGain.MovingField ActualInitialization.geometry
      (SignedMeanGain.crossTensor f a i j))
    (H : MeanStateRegularity.PrimitiveData ActualInitialization.geometry.region
      ActualInitialization.geometry.patch.a ActualInitialization.geometry.patch.b c u)
    (hfixed : (VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge c u).pressure
        = u.pressure)
    (hθ : WeightedClasses.MeanClass ActualInitialization.geometry.strip (1 + σ - κ)
        (u.thetaResidual c))
    (hz : WeightedClasses.MeanClass ActualInitialization.geometry.strip (1 + σ - κ)
        (u.axialResidual c)) :
    ∀ γ : ℝ,
      WeightedClasses.MeanClass ActualInitialization.geometry.strip γ
        (StateMomentBalances.meanBar (SignedMeanGain.crossTensor f a 0 1) -
          SignedMeanGain.physicalSigma ActualInitialization.geometry 2 (u.thetaResidual c)) ∧
      WeightedClasses.MeanClass ActualInitialization.geometry.strip γ
        (StateMomentBalances.meanBar (SignedMeanGain.crossTensor f a 0 2) -
          SignedMeanGain.physicalSigma ActualInitialization.geometry 1 (u.axialResidual c)) := by
  apply SignedCrossDefectClass.residual_defects_all_exponents_of_primitive
    ActualInitialization.geometry c u f a hS H hfixed hθ hz ((choice B N0).prepared.N + 1)
  intro n hn x hx i
  exact family_requested_cross_tail c u f a hprimary htangent hlabels hn hx i

end Family

end NavierStokes.ActualSignedMeanBinding

end
end

end

section

/-!
# Gaussian cutoff errors of the actual signed correction

The transverse cutoff and the Gaussian cutoff remain in the literal
native cutoff.  The transverse factor has zero fast derivative.  Thus
the actual error vanishes on the central Gaussian plateau and retains
the exact square-root edge weight at every decay exponent.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.ActualSignedGaussian

open Set Function Filter WeightedClasses CorrectionInitialization
open ActualSignedStageControls
open scoped ContDiff Topology BigOperators

variable {B N0 : ℕ}

/-- Copies, given by `(parameters l).copyData ActualPrimaryBounds.strip request`. -/
noncomputable def copies (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (l : SignedLabel B N0) : PeriodizedWaveBounds.CopyData FullPoint Frequency :=
  (parameters l).copyData ActualPrimaryBounds.strip request

/-- Local gaussian, given by `(copies request l).localGaussian (directions B) n k`. -/
noncomputable def localGaussian (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (l : SignedLabel B N0) (n : ℕ) (k : Frequency) : FullPoint → HarmonicCalculus.ComplexVector :=
  (copies request l).localGaussian (directions B) n k

theorem source_zero (request : ℕ → FullPoint → SignedWaveUpdate.Vec2) (l : SignedLabel B N0) :
    (copies request l).source = fun _ _ => 0 := rfl

theorem localGaussian_formula (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (l : SignedLabel B N0) (n : ℕ) (k : Frequency) (x : FullPoint) :
    localGaussian request l n k x =
      (directions B).Dfast (cutoff l k) n x • (copies request l).amplitude n k x := by
  unfold localGaussian
  rw [PeriodizedWaveBounds.CopyData.localGaussian_eq]
  change _ + (1 - cutoff l k n x) • (0 : HarmonicCalculus.ComplexVector) = _
  simp only [smul_zero, add_zero]
  rfl

/-- Transverse, given by `PartitionedCovariance.cutoff ActualPrimary.slots.radius (nativePoint l
n k x).2.1`. -/
noncomputable def transverse (l : SignedLabel B N0) (k : Frequency) (n : ℕ)
    (x : FullPoint) : ℝ :=
  PartitionedCovariance.cutoff ActualPrimary.slots.radius (nativePoint l n k x).2.1

theorem transverse_smooth (l : SignedLabel B N0) (n : ℕ) (k : Frequency) :
    ContDiff ℝ ∞ (transverse l k n) :=
  (SquaredPartition.gridMask_smooth ActualPrimary.slots.radius 0).comp
    (nativePoint_smooth l n k).snd.fst

/-- Only the native clock changes along the fast direction. -/
theorem transverse_fast_zero (l : SignedLabel B N0) (n : ℕ) (k : Frequency) (x : FullPoint) :
    (directions B).Dfast (transverse l k) n x = 0 := by
  have hd : HasDerivAt (fun _ : ℝ =>
      PartitionedCovariance.cutoff ActualPrimary.slots.radius (nativePoint l n k x).2.1)
      0 (nativePoint l n k x).2.2 := hasDerivAt_const _ _
  have h := ActualPrimaryDynamics.along_copy l.2 l.1 n k
    (fun y => PartitionedCovariance.cutoff ActualPrimary.slots.radius y.2.1) hd
    ((transverse_smooth l n k).differentiable (by simp)).differentiableAt
  simp only [smul_zero] at h
  exact h

/-- The product cutoff is differentiated literally. The transverse
derivative term vanishes; no cutoff factor is silently moved into the mask. -/
theorem cutoff_fast (l : SignedLabel B N0) (n : ℕ) (k : Frequency) (x : FullPoint) :
    (directions B).Dfast (cutoff l k) n x =
      transverse l k n x * (directions B).Dfast
        (fun m y => GaussianTailFlat.profile (nativeTime l m k y)) n x := by
  have ht := ((transverse_smooth l n k).differentiable (by simp)).differentiableAt (x := x)
  have hg := ((GaussianTailFlat.profile_contDiff.comp (nativeTime_smooth l n k)).differentiable
    (by simp)).differentiableAt (x := x)
  simp only [Function.comp_def] at hg
  have hz := transverse_fast_zero l n k x
  change fderiv ℝ (transverse l k n) x ((directions B).fastField n x) = 0 at hz
  change fderiv ℝ (fun y => transverse l k n y * GaussianTailFlat.profile (nativeTime l n k y))
    x ((directions B).fastField n x) =
      transverse l k n x * fderiv ℝ (fun y => GaussianTailFlat.profile (nativeTime l n k y))
        x ((directions B).fastField n x)
  rw [fderiv_fun_mul ht hg]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, hz]
  ring

/-- The central Gaussian plateau kills the actual error even when the
transverse cutoff is strictly between zero and one. -/
theorem localGaussian_zero_plateau (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (l : SignedLabel B N0) (n : ℕ) (k : Frequency) {x : FullPoint}
    (hm : |nativeTime l n k x - 1 / 2| < 1 / 5) :
    localGaussian request l n k =ᶠ[𝓝 x] fun _ => 0 := by
  have hg := (GaussianTailFlat.profile_eventually_one hm).comp_tendsto
    (nativeTime_smooth l n k).continuous.continuousAt.tendsto
  have hc : cutoff l k n =ᶠ[𝓝 x] transverse l k n := by
    filter_upwards [hg] with y hy
    change GaussianTailFlat.profile (nativeTime l n k y) = 1 at hy
    change transverse l k n y * GaussianTailFlat.profile (nativeTime l n k y) = transverse l k n y
    rw [hy, mul_one]
  have hd := ParticularWaveAssembly.along_germ hc ((directions B).fastField n)
  filter_upwards [hd] with y hy
  rw [localGaussian_formula]
  change HarmonicCalculus.along ((directions B).fastField n) (cutoff l k n) y • _ = 0
  rw [hy]
  change (directions B).Dfast (transverse l k) n y • _ = 0
  rw [transverse_fast_zero, zero_smul]

theorem localGaussian_zero_of_cutoff (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (l : SignedLabel B N0) {n : ℕ} {k : Frequency} {x : FullPoint}
    (hz : cutoff l k n =ᶠ[𝓝 x] fun _ => 0) :
    localGaussian request l n k =ᶠ[𝓝 x] fun _ => 0 :=
  LocalizedGaussianBounds.localGaussian_zero_of_cutoff_source (copies request l) (directions B)
    hz (Filter.Eventually.of_forall (fun _ => rfl))

theorem localGaussian_zero_of_mask (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (l : SignedLabel B N0) {n : ℕ} {k : Frequency} {x : FullPoint}
    (hz : mask l k n =ᶠ[𝓝 x] fun _ => 0) :
    localGaussian request l n k =ᶠ[𝓝 x] fun _ => 0 := by
  have ha : (copies request l).amplitude n k =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hz] with y hy
    exact ((parameters l).raw_zero_of_mask request n k y hy).1
  exact (copies request l).localGaussian_zero_of_fields (directions B) ha
    (Filter.Eventually.of_forall (fun _ => rfl))

theorem localGaussian_zero_outside_phaseCell (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (l : SignedLabel B N0) (n : ℕ) (k : Frequency) {x : FullPoint}
    (hx : x ∈ fullStrip.domain) (hc : x ∉ phaseCell l n k) :
    localGaussian request l n k =ᶠ[𝓝 x] fun _ => 0 := by
  rcases ActualWaveRegularityData.signed_phaseCell_or_zero l n k hx with h | h | h
  · exact (hc h).elim
  · exact localGaussian_zero_of_cutoff request l h
  · exact localGaussian_zero_of_mask request l h

/-- Band scales, bundling `power`, `epsilon_eq`, `boundConstant`, `constant_one_le` and the
required compatibility proofs. -/
noncomputable def bandScales : GaussianTailFlat.BandScaleControl fullStrip where
  power := ActualPrimary.h
  epsilon_eq := fun _ => rfl
  boundConstant := 1
  constant_one_le := le_rfl
  degree := 1
  slow_le := fun n => by
    change max 1 (ChartScales.S n) ≤ 1 * (1 + ChartScales.S n) ^ 1
    simp only [pow_one, one_mul]
    have hS : 0 ≤ ChartScales.S n := by unfold ChartScales.S; positivity
    exact max_le (by linarith) (by linarith)

theorem envelope_gaussian (l : SignedLabel B N0) (n : ℕ) (k : Frequency)
    {x : FullPoint} (hc : x ∈ phaseCell l n k) :
    envelope l n x ≤ Real.exp (-ActualInitialExcluded.gaussianRate B N0 *
      (nativeTime l n k x - 1 / 2)^2 * ActualInitialExcluded.gaussianLength (l.2,l.1) n) := by
  have he : envelope l n x = ActualPrimaryBounds.pulseEnvelope (l.2,l.1)
      (ActualPrimaryBounds.fullCopy (l.2,l.1) n k x).2.2 :=
    ActualPrimaryBounds.envelope_copy (l.2,l.1) n k hc.1.2.2.1
  rw [he, ActualInitialExcluded.gaussianLength_eq (l.2,l.1) n hc.1.1]
  have hh := ActualInitialExcluded.nativeEnvelope_gaussian (l.2,l.1) hc.1.2.2.1.2
  simp only [nativeTime, nativePoint_eq_fullCopy l n k hc.1.1] at hh ⊢
  exact hh

/-! ## Uniform Gaussian absorption with the edge weight retained -/

theorem localGaussian_wave_jets {σ : ℝ}
    {request : ℕ → FullPoint → SignedWaveUpdate.Vec2}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) σ (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request n x q)) :
    LocalizedWaveBounds.LocalWave fullStrip
      (fun n (i : SignedLabel B N0 × Frequency) => phaseCell i.1 n i.2)
      (fun n i x => envelope i.1 n x) (σ + 1 / 2)
      (fun n i => localGaussian request i.1 n i.2) := by
  have hw : ∀ l n x, x ∈ fullStrip.domain →
      0 ≤ Real.sqrt (fullStrip.zeta x) * envelope (B := B) (N0 := N0) l n x :=
    fun l n x _ => mul_nonneg (Real.sqrt_nonneg _)
      (ActualPrimaryBounds.fullEnvelope_nonneg (l.2,l.1) n x)
  have hu := LocalizedWaveBounds.LocalClass.of_uniformLocalJets hw
    (raw_coefficients_jets hR).1
  have hψ := LocalizedWaveBounds.LocalClass.of_uniformLocalJets
    (fun _ _ _ _ => zero_le_one) (cutoff_local_jets (B := B) (N0 := N0))
  have hf : LocalizedWaveBounds.LocalWave fullStrip
      (fun n (i : SignedLabel B N0 × Frequency) => phaseCell i.1 n i.2)
      (fun n i x => envelope i.1 n x) (σ + 1 / 2)
      (fun _ _ (_ : FullPoint) => (0 : HarmonicCalculus.ComplexVector)) :=
    LocalizedWaveBounds.LocalClass.zero (fun n i x hx => hw i.1 n x hx)
  have hfast : BandBound fullStrip 0 (directions B).fastScale :=
    (ActualPrimaryBounds.actual_local_inputs (B := B) (N0 := N0)).fast_scale
  exact LocalizedGaussianBounds.indexedCutoffError_wave_class (directions B) hψ hfast hu hf

/-- All joint jets of the literal local Gaussian error have every
epsilon exponent, with exactly the square-root edge weight. -/
theorem localGaussian_all_gains {σ : ℝ}
    {request : ℕ → FullPoint → SignedWaveUpdate.Vec2}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) σ (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request n x q)) (β : ℝ) :
    PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => Real.sqrt (fullStrip.zeta x)) β
      (fun l : SignedLabel B N0 => (cells l).carrier)
      (fun l n k => localGaussian request l n k) := by
  have hflat := ActualGaussianCoverage.indexed_gaussian_weighted_all_gains
    (localGaussian_wave_jets hR) bandScales
    (fun n i x => nativeTime i.1 n i.2 x)
    (fun n i => ActualInitialExcluded.gaussianLength (i.1.2,i.1.1) n)
    (fun n i => ActualInitialExcluded.gaussianLength_pos (i.1.2,i.1.1) n)
    ActualInitialExcluded.gaussianLengthLower ActualInitialExcluded.gaussianLengthLower_pos
    (fun _ _ => le_max_right _ _) (ActualInitialExcluded.gaussianRate_pos B N0)
    (fun n i _ _ hi => envelope_gaussian i.1 n i.2 hi)
    (fun n i _ _ _ hm => localGaussian_zero_plateau request i.1 n i.2 hm) β
  have hlarge : LocalizedWaveBounds.LocalClass fullStrip
      (fun n (i : SignedLabel B N0 × Frequency) => (cells i.1).carrier n i.2)
      (fun _ _ x => Real.sqrt (fullStrip.zeta x)) β
      (fun n i => localGaussian request i.1 n i.2) := by
    apply hflat.enlarge
    intro n i x hx _
    by_cases hc : x ∈ phaseCell i.1 n i.2
    · exact Or.inl hc
    · exact Or.inr (localGaussian_zero_outside_phaseCell request i.1 n i.2 hx hc)
  exact hlarge.to_uniformLocalJets

/-- Global gaussian, given by `(copies request l).globalGaussian (directions B)`. -/
noncomputable def globalGaussian (request : ℕ → FullPoint → SignedWaveUpdate.Vec2)
    (l : SignedLabel B N0) : ℕ → FullPoint → HarmonicCalculus.ComplexVector :=
  (copies request l).globalGaussian (directions B)

/-- The actual periodized Gaussian coefficient, including its source
complement, has the exact weighted class. The signed source is identically zero. -/
theorem globalGaussian_all_gains {σ : ℝ}
    {request : ℕ → FullPoint → SignedWaveUpdate.Vec2}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) σ (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request n x q)) (β : ℝ) :
    LabelSumBounds.UniformClass fullStrip
      (fun _ _ x => Real.sqrt (fullStrip.zeta x)) β
      (globalGaussian (B := B) (N0 := N0) request) := by
  have hf : LocalizedGaussianBounds.UniformComplementJets fullStrip
      (fun _ _ x => Real.sqrt (fullStrip.zeta x)) β
      (fun l : SignedLabel B N0 => (cells l).carrier)
      (fun l => (copies request l).source) :=
    LocalizedGaussianBounds.UniformComplementJets.of_zero_germs fullStrip _ β _ _
      (fun _ _ _ _ _ => Filter.Eventually.of_forall (fun _ => rfl))
  exact LocalizedGaussianBounds.uniform_globalGaussian_class_with_complement
    (copies request) cells (fun l n k => cutoff_support l n k) (directions B)
    (fun _ _ _ _ => Real.sqrt_nonneg _) (localGaussian_all_gains hR β) hf

/-- This is the precise Fourier-coefficient class required by the signed
Gaussian field of `CorrectionAnalyticStep.WaveData`. -/
theorem gaussianBlock_jets {σ : ℝ}
    {request : ℕ → FullPoint → SignedWaveUpdate.Vec2}
    (hR : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) σ (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => request n x q)) (β : ℝ) (i : Fin 3) (j : ℤ) :
    LabelSumBounds.UniformClass ActualPrimaryBounds.strip
      (fun _ _ x => Real.sqrt (ActualPrimaryBounds.strip.zeta x)) β
      (fun l : SignedLabel B N0 => fun n x =>
        ((parameters l).gaussianBlock ActualPrimaryBounds.strip request).velocity n i j x) := by
  have hg : LabelSumBounds.UniformClass
      (HarmonicWaveInteraction.productStrip ActualPrimaryBounds.strip)
      (fun (_ : SignedLabel B N0) (_ : ℕ) (x : FullPoint) =>
        Real.sqrt (ActualPrimaryBounds.strip.zeta x.1)) β
      (globalGaussian request) := globalGaussian_all_gains hR β
  have hs := UniformBlockBounds.uniform_slice
    (s := ActualPrimaryBounds.strip)
    (w := fun (_ : SignedLabel B N0) (_ : ℕ) (x : Point) =>
      Real.sqrt (ActualPrimaryBounds.strip.zeta x)) hg
  have hi := hs.map (ContinuousLinearMap.proj i)
  exact UniformBlockBounds.pair_uniform hi 1 j

/-- Actual current residuals and primitive identities supply the request
jet premise; no signed Gaussian output estimate is an input. -/
theorem actual_gaussianBlock_jets (G : SignedMeanGain.Geometry)
    (hs : G.strip = ActualPrimaryBounds.strip)
    (c : CorrectionState.Context Point) (u : CorrectionState.State Point) (α : ℝ)
    (H : MeanStateRegularity.PrimitiveData G.region G.patch.a G.patch.b c u)
    (hfixed : VariableGaugeMean.reconstructState G.gauge c u = u)
    (hθ : MeanClass G.strip α (u.thetaResidual c))
    (hz : MeanClass G.strip α (u.axialResidual c)) (β : ℝ) (i : Fin 3) (j : ℤ) :
    LabelSumBounds.UniformClass ActualPrimaryBounds.strip
      (fun _ _ x => Real.sqrt (ActualPrimaryBounds.strip.zeta x)) β
      (fun l : SignedLabel B N0 => fun n x =>
        ((parameters l).gaussianBlock ActualPrimaryBounds.strip
          (LocalSignedRequest.fullRequest G.strip G.patch G.coord c u)).velocity n i j x) := by
  have hr := fullRequest_jets_from_residuals G c u α H hfixed hθ hz
    (phaseCell (B := B) (N0 := N0))
  have hr' : ∀ q, PeriodizedWaveBounds.UniformLocalJets fullStrip
      (fun _ _ x => fullStrip.zeta x) (α - 1) (phaseCell (B := B) (N0 := N0))
      (fun _ n _ x => LocalSignedRequest.fullRequest G.strip G.patch G.coord c u n x q) := by
    simp only [hs] at hr ⊢
    exact hr
  exact gaussianBlock_jets hr' β i j

end NavierStokes.ActualSignedGaussian

end
end

end

section

/-!
# Measured debt before the actual rank correction

The first-wave debt, the signed covariance change, and the temporal mean
change are evaluated on the literal intermediate states.  No estimate of
the post-temporal debt is supplied as a premise.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.ActualIntermediateDebtBounds

open Set Function WeightedClasses MeanIncrementBounds CorrectionState CorrectionStep
open CorrectionInitialization VariableGaugeMean
open scoped ContDiff Topology BigOperators

/-- Point: an abbreviation for `ActualInitialization.Point`. -/
abbrev Point := ActualInitialization.Point
/-- Index: an abbreviation for `ActualInitialization.Index B N0`. -/
abbrev Index (B N0 : ℕ) := ActualInitialization.Index B N0

/-- Signed velocity: an abbreviation for `(ActualCycleParameters.fixedParameters B
N0).signedVelocity x.coefficients (ActualPrimary.commonContext B) x.state`. -/
noncomputable abbrev signedVelocity {B N0 : ℕ} (x : CycleState (Index B N0)) :=
  (ActualCycleParameters.fixedParameters B N0).signedVelocity x.coefficients
    (ActualPrimary.commonContext B) x.state

/-- Signed pressure: an abbreviation for `(ActualCycleParameters.fixedParameters B
N0).signedPressure x.coefficients (ActualPrimary.commonContext B) x.state`. -/
noncomputable abbrev signedPressure {B N0 : ℕ} (x : CycleState (Index B N0)) :=
  (ActualCycleParameters.fixedParameters B N0).signedPressure x.coefficients
    (ActualPrimary.commonContext B) x.state

/-- Signed gaussian: an abbreviation for `(ActualCycleParameters.fixedParameters B
N0).signedGaussian x.coefficients (ActualPrimary.commonContext B) x.state`. -/
noncomputable abbrev signedGaussian {B N0 : ℕ} (x : CycleState (Index B N0)) :=
  (ActualCycleParameters.fixedParameters B N0).signedGaussian x.coefficients
    (ActualPrimary.commonContext B) x.state

/-- Post signed: an abbreviation for `(ActualCycleParameters.fixedParameters B N0).afterSigned
x.coefficients (ActualPrimary.commonContext B) x.state`. -/
noncomputable abbrev postSigned {B N0 : ℕ} (x : CycleState (Index B N0)) :=
  (ActualCycleParameters.fixedParameters B N0).afterSigned x.coefficients
    (ActualPrimary.commonContext B) x.state

/-- Temporal increment: an abbreviation for `(ActualCycleParameters.fixedParameters B
N0).temporalIncrement x.coefficients (ActualPrimary.commonContext B) x.state`. -/
noncomputable abbrev temporalIncrement {B N0 : ℕ} (x : CycleState (Index B N0)) :=
  (ActualCycleParameters.fixedParameters B N0).temporalIncrement x.coefficients
    (ActualPrimary.commonContext B) x.state

/-- Post temporal: an abbreviation for `(ActualCycleParameters.fixedParameters B
N0).afterTemporal x.coefficients (ActualPrimary.commonContext B) x.state`. -/
noncomputable abbrev postTemporal {B N0 : ℕ} (x : CycleState (Index B N0)) :=
  (ActualCycleParameters.fixedParameters B N0).afterTemporal x.coefficients
    (ActualPrimary.commonContext B) x.state

section Core

variable {B N0 : ℕ} {x : CycleState (Index B N0)} {σ : ℝ}
    {S : Index B N0 → ℕ → Set Point}
    (H : CycleAnalyticInvariant ActualInitialization.geometry (ActualPrimary.commonContext B)
      ActualInitialization.tangentBlock ActualInitialization.envelope S σ x)
    (hσ : 1 / 5 ≤ σ)
    (first : ActualParticularMeanGain.Result x σ)
    (hCov : SignedMeanGain.TensorClass ActualInitialization.strip (1 + σ - ChartScales.kappa)
      (SignedMeanGain.covarianceIncrement (ActualParticularMeanGain.postParticular x).oscillation
        (signedVelocity x)))
    (hX : ∀ i j, GaugeMomentBalances.MovingField ActualPrimary.standardRegion
      ActualInitialization.patch.a ActualInitialization.patch.b
      (SignedMeanGain.covarianceIncrement (ActualParticularMeanGain.postParticular x).oscillation
        (signedVelocity x) i j))
    (hTemporal : IncrementBounds ActualInitialization.strip (1 + σ - 2 * ChartScales.kappa)
      (temporalIncrement x))

include H hσ first hCov hX hTemporal

/-- Both intermediate debts are measured from the actual state.  The
signed stage loses one operator exponent, while the temporal change
retains the exponent of its genuine mean increment. -/
theorem stage_debt_bounds :
    (∀ i : Fin 3, UnweightedClass ActualInitialization.slowStrip (1+σ-2*ChartScales.kappa)
      (fun n z => debt (ActualPrimary.commonContext B) (postSigned x) n z i)) ∧
    (∀ i : Fin 3, UnweightedClass ActualInitialization.slowStrip (1+σ-2*ChartScales.kappa)
      (fun n z => debt (ActualPrimary.commonContext B) (postTemporal x) n z i)) := by
  let G := ActualInitialization.geometry
  have hSigned := GaugeDebtIncrement.waveStage_debt_mem G.region G.patch.a_pos G.patch.a_lt_b
    G.left_pos G.right_pos G.epsilon G.slow G.epsilon_pos G.epsilon_le_one G.slow_ge_one
    G.gauge (ActualPrimary.commonContext B) (ActualParticularMeanGain.postParticular x)
    (signedVelocity x) (signedPressure x) (signedGaussian x)
    first.primitive.operators.regular first.primitive.base.smooth first.primitive.mean.regular
    (fun i j => MeanStateRegularity.MovingField.regular (first.primitive.covariance i j))
    (fun i j => MeanStateRegularity.MovingField.regular (hX i j))
    (ActualInitialization.operators B) hCov
    (show (1+σ-ChartScales.kappa)-ChartScales.kappa ≤ 1+(σ-ChartScales.kappa) by
      norm_num [ChartScales.kappa]; linarith) first.debt
  have hS : ∀ i : Fin 3, UnweightedClass ActualInitialization.slowStrip (1+σ-2*ChartScales.kappa)
      (fun n z => debt (ActualPrimary.commonContext B) (postSigned x) n z i) := by
    simp only [show (1+σ-ChartScales.kappa)-ChartScales.kappa = 1+σ-2*ChartScales.kappa by
        ring] at hSigned
    exact hSigned
  have HP : MeanStateRegularity.PrimitiveData G.region G.patch.a G.patch.b
      (ActualPrimary.commonContext B) (postSigned x) :=
    first.primitive.waveStage G.gauge (signedVelocity x) (signedPressure x) (signedGaussian x) hX
  have HPg : MeanStateRegularity.PrimitiveData G.region G.gauge.radial.inner G.gauge.radial.outer
      (ActualPrimary.commonContext B) (postSigned x) := by
    simpa only [G.inner_eq, G.outer_eq] using HP
  have hMoving := MeanStageRegularity.temporalIncrement_moving HPg G.inner_pos G.exponent_pos
    G.length_eq rfl ActualPrimary.h (CommonWindow.index ActualPrimary.h) ActualInitialization.axial
  have hRegular : GaugeDebtIncrement.RegularTriple G.region G.patch.a G.patch.b (temporalIncrement
      x) := by
    have hr := hMoving.regular
    simp only [G.inner_eq, G.outer_eq] at hr ⊢
    exact hr
  have hm : MeanIncrementBounds.CumulativeBounds G.strip (postSigned x).mean := by
    rw [(ActualCycleParameters.fixedParameters B N0).afterSigned_mean]
    exact H.cumulative.velocity
  have hT := GaugeDebtIncrement.temporalStage_debt_mem G.region G.patch.a_pos G.patch.a_lt_b
    G.left_pos G.right_pos G.epsilon G.slow G.epsilon_pos G.epsilon_le_one G.slow_ge_one
    G.gauge ActualPrimary.h (CommonWindow.index ActualPrimary.h) ActualInitialization.axial
    (ActualPrimary.commonContext B) (postSigned x) HP.operators.regular HP.base.smooth
        HP.mean.regular
    hRegular (fun i j => MeanStateRegularity.MovingField.regular (HP.covariance i j))
    (ActualInitialization.operators B) (ActualInitialization.base_bounds B) hm hTemporal
    (show 9/10 ≤ 1+σ-2*ChartScales.kappa by norm_num [ChartScales.kappa]; linarith)
    (show 2*ChartScales.kappa ≤ 9/10 by norm_num [ChartScales.kappa]) le_rfl hS
  exact ⟨hS, hT⟩

end Core

section FromStepData

variable {B N0 : ℕ} {x : CycleState (Index B N0)} {σ : ℝ}
    {S : Index B N0 → ℕ → Set Point}
    (D : CorrectionAnalyticStep.StaticData ActualInitialization.geometry ActualPrimary.h
      (CommonWindow.index ActualPrimary.h) ActualInitialization.axial ActualPrimary.rankData
      (ActualPrimary.commonContext B) ChartScales.kappa)
    (H : CycleAnalyticInvariant ActualInitialization.geometry (ActualPrimary.commonContext B)
      ActualInitialization.tangentBlock ActualInitialization.envelope S σ x)
    (hσ : 1 / 5 ≤ σ) (particular : ActualParticularMeanGain.Inputs x σ)
    (d : CorrectionAnalyticStep.StepData ActualInitialization.geometry ActualPrimary.h
      (CommonWindow.index ActualPrimary.h) ActualInitialization.axial
      (fun l => ActualParticularStageControls.canonicalParameters (ActualCycleParameters.swap B N0
          l))
      ActualSignedStageControls.parameters ActualPrimary.rankData (ActualPrimary.commonContext B)
      x ActualInitialization.tangentBlock ActualInitialization.envelope S D H hσ)

include D H hσ particular d

/-- Concrete factory-facing form.  Both covariance and temporal estimates
are derived from the checked step data, and the initial intermediate debt
is derived from the particular inputs. -/
theorem stage_debt_from_stepData :
    (∀ i : Fin 3, UnweightedClass ActualInitialization.slowStrip (1+σ-2*ChartScales.kappa)
      (fun n z => debt (ActualPrimary.commonContext B) (postSigned x) n z i)) ∧
    (∀ i : Fin 3, UnweightedClass ActualInitialization.slowStrip (1+σ-2*ChartScales.kappa)
      (fun n z => debt (ActualPrimary.commonContext B) (postTemporal x) n z i)) := by
  let p := ActualCycleParameters.fixedParameters B N0
  let c := ActualPrimary.commonContext B
  let W := d.waves
  let F := p.signedFamily x.coefficients c x.state ActualInitialization.tangentBlock
    ActualInitialization.envelope hσ d.primaryBand d.primary_band H.bands H.carrier W.carrier
    H.wave H.difference W.particular W.tangent W.curl d.envelope_nonneg d.envelope_le_one H.angular
  let a : SignedMeanGain.Assembly F := d.assembly
  have hlabels : a.labels = x.coefficients.labels := d.labels
  have hOld : (ActualParticularMeanGain.postParticular x).oscillation = SignedMeanGain.oldField F a
      := by
    simpa only [SignedMeanGain.oldField, F, CycleParameters.signedFamily, hlabels] using
      p.beforeSignedBlock_represents x.coefficients c x.state H.representation
  have hWave : SignedMeanGain.tangentField F a + SignedMeanGain.curlField F a = signedVelocity x :=
      by
    simpa only [SignedMeanGain.tangentField, SignedMeanGain.curlField, F,
      CycleParameters.signedFamily, hlabels] using (p.signedVelocity_split x.coefficients c
          x.state).symm
  have hCov : SignedMeanGain.TensorClass ActualInitialization.strip (1+σ-ChartScales.kappa)
      (SignedMeanGain.covarianceIncrement (ActualParticularMeanGain.postParticular x).oscillation
        (signedVelocity x)) := by
    have hh := (SignedMeanGain.signed_tensor_bounds hσ (by rfl) F a).1
    rwa [SignedMeanGain.incrementTensor, ← hOld, hWave] at hh
  have hX := (W.covariance_moving H.oscillationSmooth H.oscillationPeriodic).2
  have hStep := CorrectionAnalyticStep.step ActualInitialization.geometry ActualPrimary.h
    (CommonWindow.index ActualPrimary.h) ActualInitialization.axial
    (fun l => ActualParticularStageControls.canonicalParameters (ActualCycleParameters.swap B N0 l))
    ActualSignedStageControls.parameters ActualPrimary.rankData (ActualPrimary.commonContext B)
    x ActualInitialization.tangentBlock ActualInitialization.envelope S D H hσ (by rfl) d
  exact stage_debt_bounds H hσ (ActualParticularMeanGain.postParticular_gain H particular hσ)
    hCov hX hStep.temporal

/-- The full three-component slow source used by the actual rank repair. -/
theorem afterTemporal_debt_from_stepData :
    UnweightedClass ActualInitialization.slowStrip (1+σ-2*ChartScales.kappa)
      (debt (ActualPrimary.commonContext B) (postTemporal x)) :=
  RankStateBounds.debtClass_of_components ActualInitialization.slowStrip
    (stage_debt_from_stepData D H hσ particular d).2

end FromStepData

end NavierStokes.ActualIntermediateDebtBounds

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.ActualCyclePreservation

open Set Function Filter WeightedClasses CorrectionState CorrectionStep CorrectionInitialization
open scoped ContDiff Topology BigOperators

/-- Point: an abbreviation for `ActualInitialization.Point`. -/
abbrev Point := ActualInitialization.Point
/-- Index: an abbreviation for `ActualInitialization.Index local notation "G" =>
ActualInitialization.geometry local notation "κ" => ChartScales.kappa`. -/
abbrev Index := ActualInitialization.Index

local notation "G" => ActualInitialization.geometry
local notation "κ" => ChartScales.kappa

/-- One fixed similarity geometry and the actual base/rank parameters
work at every correction stage. -/
noncomputable def staticData (B : ℕ) :
    CorrectionAnalyticStep.StaticData G ActualPrimary.h
      (CommonWindow.index ActualPrimary.h) ActualInitialization.axial
      ActualPrimary.rankData (ActualPrimary.commonContext B) κ where
  aliasData := ActualCycleGeometry.similarityData
  coord := rfl
  region := HEq.rfl
  inner := rfl
  outer := rfl
  gauge := ActualCycleGeometry.gauge_eq_geometry.symm
  strip := rfl
  time := rfl
  index_eq := rfl
  operators_eq := rfl
  operators := ActualInitialization.operators B
  base := ActualInitialization.base_bounds B
  axial_eq := rfl
  temporal := rfl
  fast := fun _ => rfl
  angular_slow := by
    intro n R p hp Y
    rfl
  axial_slow := by
    intro n R p hp Y
    rfl
  rankExponent := CoordinateAlgebra.A ActualPrimary.h
  rankCoefficient := ActualPrimary.rankAmplitude
  rankParameters := ActualPrimary.rankData_parameters (G).region.carrier
  rankCoefficient_ne := ActualPrimary.rankAmplitude_pos.ne'
  rank_left := ActualPrimary.active_left_before_rank
  rank_right := ActualPrimary.rank_before_active_right

theorem kappa_small : κ ≤ 1/100000 := by norm_num [ChartScales.kappa]

theorem primary_band {B N0 : ℕ} (l : Index B N0) :
    (ActualInitialization.tangentBlock l).BandLimited 1 :=
  SignedWaveUpdate.coefficientBlock_band _ _ _ _ _

section CurrentState

variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
    {S : Index B N0 → ℕ → Set Point}
    (H : CycleAnalyticInvariant G (ActualPrimary.commonContext B)
      ActualInitialization.tangentBlock ActualInitialization.envelope S σ x)

include H

/-- Debt regularity comes from the current primitive invariant; the
reserved pure-power base model is the already proved actual base. -/
theorem rank_geometry :
    LocalRankDefect.RankGeometry (G).gauge ActualPrimary.rankData (G).region.carrier
      (ActualPrimary.commonContext B) x.state :=
  ActualPrimary.rank_geometry (G).region B x.state
    (MeanStageRegularity.debt_smooth H.primitives (G).patch.a_pos
      ((G).patch.a_lt_left.trans ((G).patch.left_lt_right.trans (G).patch.right_lt_b)))

theorem current_normal (i : Fin 3) :
    LocalizedWaveBounds.LocalUnweighted (G).strip
      (ActualInitialization.meanControlCell (B := B) (N0 := N0)) 0
      (fun n l z => HarmonicMeanInteraction.slowNormal (ActualPrimary.commonContext B)
        (staticData B).operators (fun _z hz => (staticData B).radius_pos hz)
        (x.coefficients.blocks l).phase n z i) := by
  have he :
      (fun n l z => HarmonicMeanInteraction.slowNormal (ActualPrimary.commonContext B)
        (staticData B).operators (fun _z hz => (staticData B).radius_pos hz)
        (x.coefficients.blocks l).phase n z i) =
      (fun n l z => HarmonicMeanInteraction.slowNormal (ActualPrimary.commonContext B)
        (ActualInitialization.operators B) (ActualInitialization.radius_pos B)
        (ActualInitialization.primaryBlock l).phase n z i) := by
    funext n l z
    rw [← (H.carrier l).phase]
    rfl
  rw [he]
  exact ActualInitialization.slowNormal_local B N0 i

theorem current_frequency :
    LocalizedWaveBounds.LocalUnweighted (G).strip
      (ActualInitialization.meanControlCell (B := B) (N0 := N0)) (-(1/2))
      (fun n l _ => (x.coefficients.blocks l).frequency n) := by
  have he : (fun n l (_ : Point) => (x.coefficients.blocks l).frequency n) =
      (fun n l (_ : Point) => (ActualInitialization.primaryBlock l).frequency n) := by
    funext n l z
    rw [← (H.carrier l).frequency]
    rfl
  rw [he]
  exact ActualInitialization.frequency_local B N0

theorem current_angular :
    LocalizedWaveBounds.LocalUnweighted (G).strip
      (ActualInitialization.meanControlCell (B := B) (N0 := N0)) (-(1/2))
      (fun n l _ => ((x.coefficients.blocks l).angularFrequency n : ℝ)) := by
  have he : (fun n l (_ : Point) => ((x.coefficients.blocks l).angularFrequency n : ℝ)) =
      (fun n l (_ : Point) => ((ActualInitialization.primaryBlock l).angularFrequency n : ℝ)) := by
    funext n l z
    rw [← (H.carrier l).angular]
    rfl
  rw [he]
  exact ActualInitialization.angularFrequency_local B N0

end CurrentState

/-! The actual label set is unchanged by every correction. -/

theorem step_labels {B N0 : ℕ} (x : CycleState (Index B N0)) :
    (x.step (ActualCycleParameters.fixedParameters B N0) (ActualPrimary.commonContext
        B)).coefficients.labels =
      x.coefficients.labels := rfl

/-- State, constructed using `CycleState.iterate`. -/
noncomputable def state (B N0 : ℕ) : ℕ → CycleState (Index B N0) :=
  CycleState.iterate (fun _ => ActualCycleParameters.fixedParameters B N0)
    (ActualPrimary.commonContext B) (ActualInitialization.initialCycleState B N0)

theorem state_zero (B N0 : ℕ) : state B N0 0 = ActualInitialization.initialCycleState B N0 := rfl

theorem state_succ (B N0 n : ℕ) :
    state B N0 (n+1) = (state B N0 n).step (ActualCycleParameters.fixedParameters B N0)
      (ActualPrimary.commonContext B) := rfl

theorem state_labels (B N0 n : ℕ) :
    (state B N0 n).coefficients.labels = ActualPrimary.activeLabels ActualPrimary.standardRegion B
        N0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- The fixed comparison primary is the original finite tangent field. -/
noncomputable def primaryField (B N0 : ℕ) : Oscillation Point :=
  LabelSumBounds.fieldSum (ActualPrimary.activeLabels ActualPrimary.standardRegion B N0)
    (fun l => (ActualInitialization.tangentBlock l).oscillation)

theorem primaryField_eq (B N0 : ℕ) :
    primaryField B N0 = ActualPrimaryCovariance.tangentSum B N0 := by
  funext n z i
  apply Finset.sum_congr rfl
  intro l hl
  exact congrArg (fun f : Oscillation Point => f n z i)
    (ActualInitialization.tangentBlock_represents l)

theorem primaryField_smooth (B N0 : ℕ) :
    WaveStateRegularity.AngularSmooth (G).domain (primaryField B N0) := by
  rw [primaryField_eq]
  exact ActualInitialMean.tangent_angularSmooth B N0

theorem primaryField_periodic (B N0 : ℕ) :
    OscillationPeriodic (G).region.carrier (primaryField B N0) := by
  intro n R s hs theta Y k
  funext i
  apply Finset.sum_congr rfl
  intro l hl
  simp only [ActualInitialization.tangentBlock_represents]
  have he := congrFun (ActualPrimaryCoherence.piece_tangentVelocity_periodic
      ActualPrimary.standardRegion l.2 l.1 n (ActualCycleParameters.activeLabel_index n l hl)
      k ((R, (s, Y)), theta)) i
  simp only [ActualPrimaryCoherence.chartDeck, TorusAverages.latticePoint,
    Prod.add_def, add_zero] at he
  exact he

/-- A true source core with its native dyadic restriction lies in the
existing quantitative control cell on the evaluation strip. -/
theorem meanControl_of_source_and_nativeQ {B N0 : ℕ}
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (l : Index B N0) (n : ℕ)
    {z : Point} (hz : z ∈ (G).strip.domain)
    (hS : z ∈ ActualInitialization.labelCarrier l n)
    (hQ : SimilarityHomogeneity.chartQ ActualPrimary.h
      (ActualPrimary.nativeSlow l.1 (ActualPrimary.toAbsolute n z)) ∈ Icc (1 / 2 : ℝ) 2) :
    z ∈ ActualInitialization.meanControlCell n l := by
  obtain ⟨k, hn, hcell, hclock⟩ := ActualCarrierGeometry.labelCarrier_phaseCell hN
    (l.2,l.1) n (x := (z,0)) hz hS
  refine ⟨k, hn, hcell, hclock, ?_⟩
  rw [← congrFun (ActualSignedStageControls.nativePoint_eq_fullCopy l n k hn) (z,0)]
  exact hQ

/-- Restrict a local estimate only on the actual evaluation domain. -/
theorem localUnweighted_restrict {E I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : StripData Point} {C K : ℕ → I → Set Point} {α : ℝ}
    {f : ℕ → I → Point → E}
    (h : LocalizedWaveBounds.LocalUnweighted s C α f)
    (hKC : ∀ n l z, z ∈ s.domain → z ∈ K n l → z ∈ C n l) :
    LocalizedWaveBounds.LocalUnweighted s K α f where
  weight_nonneg := h.weight_nonneg
  smooth := fun n l z hz hk => h.smooth n l z hz (hKC n l z hz hk)
  bounds := by
    intro m
    obtain ⟨A, hA, p, hb⟩ := h.bounds m
    exact ⟨A, hA, p, fun n l z hz hk j hj => hb n l z hz (hKC n l z hz hk) j hj⟩

theorem family_primary_eq {B N0 : ℕ} {α δ β η : ℝ}
    (f : LabelSumBounds.SignedFamily (G).strip
      (ActualInitialization.envelope (B := B) (N0 := N0)) α δ β η)
    (a : SignedMeanGain.Assembly f)
    (hp : f.primary = ActualInitialization.tangentBlock)
    (hl : a.labels = ActualPrimary.activeLabels ActualPrimary.standardRegion B N0) :
    SignedMeanGain.primaryField f a = primaryField B N0 := by
  simp only [SignedMeanGain.primaryField, primaryField, hp, hl]

theorem family_primary_smooth {B N0 : ℕ} {α δ β η : ℝ}
    (f : LabelSumBounds.SignedFamily (G).strip
      (ActualInitialization.envelope (B := B) (N0 := N0)) α δ β η)
    (a : SignedMeanGain.Assembly f)
    (hp : f.primary = ActualInitialization.tangentBlock)
    (hl : a.labels = ActualPrimary.activeLabels ActualPrimary.standardRegion B N0) :
    WaveStateRegularity.AngularSmooth (G).domain (SignedMeanGain.primaryField f a) := by
  rw [family_primary_eq f a hp hl]
  exact primaryField_smooth B N0

theorem family_primary_periodic {B N0 : ℕ} {α δ β η : ℝ}
    (f : LabelSumBounds.SignedFamily (G).strip
      (ActualInitialization.envelope (B := B) (N0 := N0)) α δ β η)
    (a : SignedMeanGain.Assembly f)
    (hp : f.primary = ActualInitialization.tangentBlock)
    (hl : a.labels = ActualPrimary.activeLabels ActualPrimary.standardRegion B N0) :
    OscillationPeriodic (G).region.carrier (SignedMeanGain.primaryField f a) := by
  rw [family_primary_eq f a hp hl]
  exact primaryField_periodic B N0

/-- The cycle keeps the actual closed radial and native dyadic cores. -/
abbrev Invariant {B N0 : ℕ} (σ : ℝ) (x : CycleState (Index B N0)) : Prop :=
  CycleAnalyticInvariant G (ActualPrimary.commonContext B)
    ActualInitialization.tangentBlock ActualInitialization.envelope
    ActualCoreSupport.refinedCarrier σ x

theorem core_control {B N0 : ℕ}
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (l : Index B N0) (n : ℕ)
    {z : Point} (hz : z ∈ (G).strip.domain)
    (hc : z ∈ ActualCoreSupport.refinedCarrier l n) :
    z ∈ ActualInitialization.meanControlCell n l := by
  have h := (ActualCoreSupport.mem_refinedCarrier_iff l n
    (ActualInitialization.strip_time z hz)).mp hc
  exact meanControl_of_source_and_nativeQ hN l n hz h.1 h.2.2

theorem core_normal {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
    (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (i : Fin 3) :
    LocalizedWaveBounds.LocalUnweighted (G).strip
      (fun n l => ActualCoreSupport.refinedCarrier l n) 0
      (fun n l z => HarmonicMeanInteraction.slowNormal (ActualPrimary.commonContext B)
        (staticData B).operators (fun _z hz => (staticData B).radius_pos hz)
        (x.coefficients.blocks l).phase n z i) :=
  localUnweighted_restrict (current_normal H i)
    (fun n l _z hz hc => core_control hN l n hz hc)

theorem core_frequency {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
    (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    LocalizedWaveBounds.LocalUnweighted (G).strip
      (fun n l => ActualCoreSupport.refinedCarrier l n) (-(1/2))
      (fun n l _ => (x.coefficients.blocks l).frequency n) :=
  localUnweighted_restrict (current_frequency H)
    (fun n l _z hz hc => core_control hN l n hz hc)

theorem core_angular {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
    (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) :
    LocalizedWaveBounds.LocalUnweighted (G).strip
      (fun n l => ActualCoreSupport.refinedCarrier l n) (-(1/2))
      (fun n l _ => ((x.coefficients.blocks l).angularFrequency n : ℝ)) :=
  localUnweighted_restrict (current_angular H)
    (fun n l _z hz hc => core_control hN l n hz hc)

/-- Existing estimates stated on the broad carrier apply by inclusion;
the stronger support is still retained by the cycle invariant. -/
theorem broad_invariant {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
    (H : Invariant σ x) :
    CycleAnalyticInvariant G (ActualPrimary.commonContext B)
      ActualInitialization.tangentBlock ActualInitialization.envelope
      ActualInitialization.labelCarrier σ x := by
  refine { H with inputSupport := ?_ }
  intro l
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n i j hj z hz hn
    exact (H.inputSupport l).velocity n i j hj z hz
      (fun hc => hn (ActualCoreSupport.refinedCarrier_subset_broad l n hc))
  · intro n j hj z hz hn
    exact (H.inputSupport l).pressure n j hj z hz
      (fun hc => hn (ActualCoreSupport.refinedCarrier_subset_broad l n hc))
  · intro n i j hj z hz hn
    exact (H.inputSupport l).gaussian n i j hj z hz
      (fun hc => hn (ActualCoreSupport.refinedCarrier_subset_broad l n hc))
  · intro n i j hj z hz hn
    exact (H.inputSupport l).aliasError n i j hj z hz
      (fun hc => hn (ActualCoreSupport.refinedCarrier_subset_broad l n hc))

/-- The strengthened support is already proved for the literal initial state. -/
theorem initial_invariant (B N0 : ℕ) : Invariant (1/5) (state B N0 0) :=
  ActualCoreSupport.initial_invariant B N0

theorem closed_radius_mem_closure {z : Point} (hz : z ∈ (G).domain)
    (hr : ActualCoreSupport.radialRatio z ∈ Icc (G).patch.a (G).patch.b) :
    z ∈ closure (G).strip.domain := by
  let ell := VariableGaugeMean.qLength (2 * ActualPrimary.h) z.2.1
  have hT := (G).region.time_pos z.2.1 hz
  have hp : 0 < ell := VariableGaugeMean.qLength_pos
    (by linarith [ActualPrimary.outgoing.data.h_pos])
    (by linarith [ActualPrimary.outgoing.data.h_lt_half]) hT
  let f : ℝ → Point := fun r => (r * ell, z.2)
  have hf : Continuous f := (continuous_id.mul continuous_const).prodMk continuous_const
  have hi : ActualCoreSupport.radialRatio z ∈ closure (Ioo (G).patch.a (G).patch.b) := by
    rwa [closure_Ioo ((G).patch.a_lt_left.trans
      ((G).patch.left_lt_right.trans (G).patch.right_lt_b)).ne]
  have hm : MapsTo f (Ioo (G).patch.a (G).patch.b) (G).strip.domain := by
    intro r hrr
    apply (BaseContextAssembly.nativeStrip_mem ActualPrimary.nominal ActualPrimary.standardRegion
        _).mpr
    refine ⟨hz, ?_⟩
    rw [PrimaryTargetBounds.profileRadius, BaseChartJets.normalizedCoordinates_eq]
    change r * ell / ell ∈ Ioo (G).patch.a (G).patch.b
    simpa only [mul_div_cancel_right₀ _ hp.ne'] using hrr
  have hc := hf.continuousAt.continuousWithinAt.mem_closure hi hm
  have he : f (ActualCoreSupport.radialRatio z) = z := by
    change (z.1 / ell * ell, z.2) = z
    rw [div_mul_cancel₀ _ hp.ne']
  rwa [he] at hc

theorem physicalPosition_continuous (n : ℕ) (i : Fin 3) :
    Continuous (fun z : Point => ActualPrimary.physicalPosition n z i) := by
  fin_cases i
  · exact continuous_const.mul continuous_fst
  · exact continuous_const.mul continuous_snd.fst.snd
  · exact continuous_const.mul continuous_snd.fst.fst

theorem physicalPosition_bound_closed (n : ℕ) {z : Point}
    (hz : z ∈ closure (G).strip.domain) (i : Fin 3) :
    |ActualPrimary.physicalPosition n z i| ≤ BaseContextAssembly.geometryBound
      ActualPrimary.nominal ActualPrimary.standardRegion := by
  have hc : IsClosed {x : Point | |ActualPrimary.physicalPosition n x i| ≤
      BaseContextAssembly.geometryBound ActualPrimary.nominal ActualPrimary.standardRegion} :=
    isClosed_le (physicalPosition_continuous n i).abs continuous_const
  exact closure_minimal
    (fun x hx => ActualPrimary.physicalPosition_bound ActualPrimary.standardRegion n hx i) hc hz

theorem core_near {B N0 : ℕ} (l : Index B N0) (n : ℕ) {z : Point}
    (hz : z ∈ (G).domain) (hc : z ∈ ActualCoreSupport.refinedCarrier l n) :
    ActualPrimaryBounds.near (l.2,l.1) n := by
  have hT := (G).region.time_pos z.2.1 hz
  have hcore := (ActualCoreSupport.mem_refinedCarrier_iff l n hT).mp hc
  apply ActualWaveRegularityData.near_of_native_band l n
    (p := BaseContextAssembly.slowCoordinates z) hT
  · exact hz.2
  · have hq := hcore.2.2
    change SimilarityHomogeneity.chartQ ActualPrimary.h
      (ActualPrimary.nativeSlow l.1 (ActualPrimary.toAbsolute n z)) ∈ Icc (1/2 : ℝ) 2 at hq
    rwa [ActualPrimary.nativeSlow_toAbsolute_eq_slowChange] at hq

/-- Every supported label belongs to the literal finite sum in that band,
including at the two closed radial edges. -/
theorem core_active {B N0 : ℕ} (l : Index B N0) (n : ℕ) {z : Point}
    (hz : z ∈ (G).domain) (hc : z ∈ ActualCoreSupport.refinedCarrier l n) :
    l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n := by
  have hT := (G).region.time_pos z.2.1 hz
  have hcore := (ActualCoreSupport.mem_refinedCarrier_iff l n hT).mp hc
  have hclose := closed_radius_mem_closure hz hcore.2.1
  have hslow := ActualCarrierGeometry.labelCarrier_slow_core (l.2,l.1) n hcore.1
  have hbox := ActualCarrierGeometry.nativeSlowCore_physicalBox (l.2,l.1) hslow
  rw [ActualPrimaryCovariance.nativePoint_position] at hbox
  apply (ActualPrimary.mem_activeLabels ActualPrimary.standardRegion n l.1 l.2).mpr
  apply Finset.mem_biUnion.mpr
  refine ⟨BaseChartJets.cellBand l.1, (core_near l n hz hc).2, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨(PrimaryGeometryAssembly.label ActualPrimary.nominal l.1).2, ?_, rfl⟩
  apply CommonWindow.grid_mem_of_box l.1.val.property.1 (physicalPosition_bound_closed n hclose)
  exact hbox

section SignedOutputs
variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
local notation "p" => ActualCycleParameters.fixedParameters B N0
local notation "c" => ActualPrimary.commonContext B
local notation "v" => x.coefficients
local notation "u" => x.state
local notation "post" => CycleParameters.afterParticular p v c u
local notation "request" => CycleParameters.signedRequest p v c u

theorem signed_request_jets (first : ActualParticularMeanGain.Result x σ) :
    ∀ q, PeriodizedWaveBounds.UniformLocalJets ActualSignedStageControls.fullStrip
      (fun _ _ z => ActualSignedStageControls.fullStrip.zeta z) (σ-κ)
      (ActualSignedStageControls.phaseCell (B := B) (N0 := N0))
      (fun _ n _ z => request n z q) := by
  have h := ActualSignedStageControls.fullRequest_jets_from_residuals G c post (1+σ-κ)
    first.primitive first.reconstructed first.theta first.axial
    (ActualSignedStageControls.phaseCell (B := B) (N0 := N0))
  simp only [show (1+σ-κ)-1 = σ-κ by ring] at h
  exact h

theorem signed_common_bounds (first : ActualParticularMeanGain.Result x σ) :
    ActualSignedOutputBounds.OutputBounds (B := B) (N0 := N0) request (1/2+σ-κ) := by
  have h := ActualSignedOutputBounds.actual_common_bounds (B := B) (N0 := N0)
    G rfl c post (1+σ-κ) first.primitive first.reconstructed first.theta first.axial
  simp only [show (1+σ-κ)-1/2 = 1/2+σ-κ by ring] at h
  exact h

theorem signed_block_bounds (first : ActualParticularMeanGain.Result x σ) :
    (∀ i j, LabelSumBounds.UniformWaveClass (G).strip ActualInitialization.envelope (1/2+σ-κ)
      (fun l n z => ((p).signedTangent v c u l).velocity n i j z)) ∧
    (∀ i j, LabelSumBounds.UniformWaveClass (G).strip ActualInitialization.envelope (1/2+σ-κ)
      (fun l n z => ((p).signedBlock v c u l).velocity n i j z)) ∧
    (∀ j, LabelSumBounds.UniformWaveClass (G).strip ActualInitialization.envelope (1+σ-κ)
      (fun l n z => ((p).signedBlock v c u l).pressure n j z)) ∧
    (∀ i j, LabelSumBounds.UniformWaveClass (G).strip ActualInitialization.envelope (1+σ-2*κ)
      (fun l n z => ((p).signedCurl v c u l).velocity n i j z)) ∧
    (∀ i j, LabelSumBounds.UniformWaveClass (G).strip ActualInitialization.envelope (1+σ-4*κ)
      (fun (l : Index B N0) n z => ((ActualSignedStageControls.parameters l).goodBlock (G).strip
          request).velocity n i j z)) := by
  have h := ActualSignedOutputBounds.actual_block_bounds (B := B) (N0 := N0)
    G rfl c post (1+σ-κ) first.primitive first.reconstructed first.theta first.axial
  simp only [show (1+σ-κ)-1/2 = 1/2+σ-κ by ring,
    show (1+σ-κ)-κ = 1+σ-2*κ by ring,
    show (1+σ-κ)-3*κ = 1+σ-4*κ by ring] at h
  exact h

theorem signed_gaussian_bounds (first : ActualParticularMeanGain.Result x σ)
    (β : ℝ) (i : Fin 3) (j : ℤ) :
    LabelSumBounds.UniformClass (G).strip (fun _ _ z => Real.sqrt ((G).strip.zeta z)) β
      (fun l n z => ((p).signedGaussianBlock v c u l).velocity n i j z) :=
  ActualSignedGaussian.actual_gaussianBlock_jets (B := B) (N0 := N0)
    G rfl c post (1+σ-κ) first.primitive first.reconstructed first.theta first.axial β i j

theorem signed_coefficients_smooth (first : ActualParticularMeanGain.Result x σ)
    (l : Index B N0) (n : ℕ) (i : Fin 3) :
    HarmonicResidual.SmoothCoefficients (G).domain (((p).signedBlock v c u l).velocity n i) :=
  ActualWaveRegularityData.signed_exact_coefficients_smooth l request
    ((signed_common_bounds first).amplitude.each l) n i

theorem signed_pressure_coefficients_smooth (first : ActualParticularMeanGain.Result x σ)
    (l : Index B N0) (n : ℕ) :
    HarmonicResidual.SmoothCoefficients (G).domain (((p).signedBlock v c u l).pressure n) :=
  ActualWaveRegularityData.signed_pressure_coefficients_smooth l request
    ((signed_common_bounds first).pressure.each l) n

theorem signed_gaussian_coefficients_smooth (first : ActualParticularMeanGain.Result x σ)
    (l : Index B N0) (n : ℕ) (i : Fin 3) :
    HarmonicResidual.SmoothCoefficients (G).domain (((p).signedGaussianBlock v c u l).velocity n i)
        :=
  ActualWaveRegularityData.signed_gaussian_coefficients_smooth l request
    ((ActualSignedGaussian.globalGaussian_all_gains (signed_request_jets first) 0).each l) n i

theorem signed_field_smooth (first : ActualParticularMeanGain.Result x σ) :
    WaveStateRegularity.AngularSmooth (G).domain ((p).signedVelocity v c u) := by
  intro n i
  apply ContDiffOn.sum
  intro l hl
  exact ActualWaveRegularityData.signed_exact_smooth l (G).patch (G).coord c post
    ((signed_common_bounds first).amplitude.each l) n i

theorem signed_field_periodic :
    OscillationPeriodic (G).region.carrier ((p).signedVelocity v c u) := by
  intro n R z hz theta Y k
  funext i
  apply Finset.sum_congr rfl
  intro l hl
  exact congrFun (ActualWaveRegularityData.signed_block_periodic l (G).strip (G).patch (G).coord
    c post n R z hz theta Y k) i

theorem signed_field_support :
    WaveStateRegularity.WaveSupport (G).region (G).patch.a (G).patch.b ((p).signedVelocity v c u)
        := by
  apply WaveStateRegularity.fieldSum_support
  intro n l hl theta i z hz hn
  exact ActualWaveRegularityData.signed_exact_support l (G).patch (G).coord c post
    n theta i z hz hn

theorem signed_pressure_field_smooth (first : ActualParticularMeanGain.Result x σ) (n : ℕ) :
    ContDiffOn ℝ ∞ ((p).signedPressure v c u n) ((G).domain ×ˢ (univ : Set ℝ)) := by
  apply ContDiffOn.sum
  intro l hl
  exact ActualWaveRegularityData.signed_pressure_smooth l (G).patch (G).coord c post
    ((signed_common_bounds first).pressure.each l) n

theorem signed_tangent_field_smooth (first : ActualParticularMeanGain.Result x σ) :
    WaveStateRegularity.AngularSmooth (G).domain
      (LabelSumBounds.fieldSum (v).labels (fun l => ((p).signedTangent v c u l).oscillation)) := by
  intro n i
  apply ContDiffOn.sum
  intro l hl
  exact ActualWaveRegularityData.signed_tangent_smooth l (G).patch (G).coord c post
    ((signed_common_bounds first).amplitude.each l) n i

theorem signed_tangent_field_periodic :
    OscillationPeriodic (G).region.carrier
      (LabelSumBounds.fieldSum (v).labels (fun l => ((p).signedTangent v c u l).oscillation)) := by
  intro n R z hz theta Y k
  funext i
  apply Finset.sum_congr rfl
  intro l hl
  exact congrFun (ActualWaveRegularityData.signed_tangent_periodic l (G).patch (G).coord c post
    n R z hz theta Y k) i

theorem signed_tangent_field_support :
    WaveStateRegularity.WaveSupport (G).region (G).patch.a (G).patch.b
      (LabelSumBounds.fieldSum (v).labels (fun l => ((p).signedTangent v c u l).oscillation)) := by
  apply WaveStateRegularity.fieldSum_support
  intro n l hl theta i z hz hn
  exact ActualWaveRegularityData.signed_tangent_support l (G).patch (G).coord c post
    n theta i z hz hn

end SignedOutputs

section Assembly
variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
local notation "p" => ActualCycleParameters.fixedParameters B N0
local notation "c" => ActualPrimary.commonContext B
local notation "v" => x.coefficients
local notation "u" => x.state

theorem particular_inputs (H : Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (ha : ∀ i j, LabelSumBounds.UniformWaveClass (G).strip ActualInitialization.envelope
      (1 / 2 + σ) (fun l n z => ((p).particularBlock v c u l).velocity n i j z))
    (hs : WaveStateRegularity.AngularSmooth (G).domain ((p).particularVelocity v c u))
    (hp : OscillationPeriodic (G).region.carrier ((p).particularVelocity v c u))
    (hr : WaveStateRegularity.WaveSupport (G).region (G).patch.a (G).patch.b
      ((p).particularVelocity v c u)) :
    ActualParticularMeanGain.Inputs x σ where
  amplitude := ha
  smooth := hs
  periodic := hp
  supported := hr
  old_support := ActualCycleAssembly.old_supported x H hN
    ActualCoreSupport.refinedCarrier_subset_broad
  particular_support := ActualCycleAssembly.particular_supported_of_inputSupport x hN
    (ActualCycleAssembly.cycle_particular_inputSupport hN x c (broad_invariant H).inputSupport)

/-- Step data of waves used in actual cycle preservation. -/
noncomputable def stepDataOfWaves (H : Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (hσ : 1 / 5 ≤ σ)
    (hl : (v).labels = ActualPrimary.activeLabels ActualPrimary.standardRegion B N0)
    (W : CorrectionAnalyticStep.WaveData G p v c u ActualInitialization.envelope
      ActualCoreSupport.refinedCarrier σ κ) :
    CorrectionAnalyticStep.StepData G ActualPrimary.h (CommonWindow.index ActualPrimary.h)
      ActualInitialization.axial
      (fun l => ActualParticularStageControls.canonicalParameters (l.2,l.1))
      ActualSignedStageControls.parameters ActualPrimary.rankData c x
      ActualInitialization.tangentBlock ActualInitialization.envelope
      ActualCoreSupport.refinedCarrier (staticData B) H hσ := by
  let hP0 := fun (l : Index B N0) n z (_hz : z ∈ (G).strip.domain) =>
    ActualInitialization.envelope_nonneg l n z
  let hP1 := fun (l : Index B N0) n z (_hz : z ∈ (G).strip.domain) =>
    ActualInitialization.envelope_le_one l n z
  let a := ActualCycleAssembly.assembly x H hσ W.particular W.tangent W.curl hP0 hP1 hN
    ActualCoreSupport.refinedCarrier_subset_broad
  have hs := ActualCycleAssembly.assembly_supports x H hσ W.particular W.tangent W.curl
    hP0 hP1 hN ActualCoreSupport.refinedCarrier_subset_broad
  have ha : a.labels = ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 :=
    hs.1.trans hl
  refine {
    waves := W
    primaryBand := 1
    primary_band := primary_band
    envelope_nonneg := hP0
    envelope_le_one := hP1
    cells := fun n l => ActualCoreSupport.refinedCarrier l n
    carrier_closed := ActualCoreSupport.refinedCarrier_closed
    carrier_cells := fun _ _ => Subset.rfl
    normal := core_normal H hN
    frequency := core_frequency H hN
    angular := core_angular H hN
    assembly := a
    labels := hs.1
    old_support := hs.2.1
    particular_support := hs.2.2
    primary_smooth := family_primary_smooth _ a rfl ha
    primary_periodic := family_primary_periodic _ a rfl ha
    rank_geometry := rank_geometry H
    tailStart := (ActualPrimary.choice B N0).prepared.N + 1
    cross_tail := ?_ }
  intro n hn z hz i
  exact ActualSignedMeanBinding.family_requested_cross_tail c
    ((p).afterParticular v c u) _ a rfl rfl ha hn hz i

end Assembly

/-- In a band with no compatible common cover, the actual incoming
source has a zero germ throughout the complete slow cylinder. -/
theorem residualSource_zero_germ_of_not_ordered {B N0 : ℕ} {σ : ℝ}
    {x : CycleState (Index B N0)} (H : Invariant σ x)
    (l : Index B N0) (n : ℕ) (hn : ¬ActualWaveRegularityData.Ordered l n)
    (j : ℤ) {z : Point} (hz : z ∈ (G).domain) :
    ParticularWaveAssembly.residualSource (ActualPrimary.commonContext B) x.state
      (x.coefficients.blocks l) (x.coefficients.gaussian l)
      (x.coefficients.aliasCoefficients l) j n =ᶠ[𝓝 z] fun _ => 0 := by
  apply HarmonicSourceSupport.residualSource_zero_germ_on _ _ _ _ _
    (G).domain_open (ActualCoreSupport.refinedCarrier_closed l) (H.inputSupport l) j n hz
  intro hc
  exact hn (ActualCycleParameters.activeLabel_index n l (core_active l n hz hc))

section SignedEquations
variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
local notation "p" => ActualCycleParameters.fixedParameters B N0
local notation "c" => ActualPrimary.commonContext B
local notation "v" => x.coefficients
local notation "u" => x.state
local notation "post" => CycleParameters.afterParticular p v c u
local notation "request" => CycleParameters.signedRequest p v c u

theorem signed_solenoidal (first : ActualParticularMeanGain.Result x σ) (l : Index B N0) :
    HarmonicWaveInteraction.ModeSolenoidal (G).strip c ((p).signedBlock v c u l) :=
  ActualSignedCommonDynamics.actual_modeSolenoidal G rfl post (1+σ-κ)
    first.primitive first.reconstructed first.theta first.axial l

theorem signed_linear_bounds (H : Invariant σ x)
    (first : ActualParticularMeanGain.Result x σ) :
    UniformHarmonicInteraction.UniformVelocity (G).strip ActualInitialization.envelope
      (1+σ-4*κ) (fun l => HarmonicWaveInteraction.linearGoodBlock c
        ((p).beforeSignedBlock v c u l) ((p).signedBlock v c u l)
        ((p).signedGaussianBlock v c u l).velocity) := by
  have hc (l : Index B N0) : SameCarrier ((p).beforeSignedBlock v c u l)
      ((p).signedBlock v c u l) := by
    have h := ActualCycleParameters.invariant_fixedParameters_signed_carrier H l
    exact ⟨h.frequency,h.phase,h.angular⟩
  have h := ActualSignedCommonDynamics.actual_linearGood_bounds G rfl post (1+σ-κ)
    first.primitive first.reconstructed first.theta first.axial
    ((p).beforeSignedBlock v c u) hc
  simp only [show (1+σ-κ)-3*κ = 1+σ-4*κ by ring] at h
  exact h

theorem signed_inputSupport (l : Index B N0) :
    HarmonicSourceSupport.InputSupportOn (G).domain (ActualCoreSupport.refinedCarrier l)
      ((p).signedBlock v c u l) ((p).signedGaussianBlock v c u l).velocity 0 :=
  ActualCycleAssembly.refined_signed_inputSupport l (G).strip request

end SignedEquations

/-- Native particular data used in actual cycle preservation. -/
noncomputable def nativeParticularData {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) (j : ℤ) :=
  (ActualParticularStageControls.canonicalParameters (l.2,l.1)).copyData
    (StateReindex.context cycleAssoc.symm (ActualPrimary.commonContext B))
    (StateReindex.state cycleAssoc.symm x.state)
    (StateReindex.block cycleAssoc.symm (x.coefficients.blocks l))
    (StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.gaussian l))
    (StateReindex.blockCoefficients cycleAssoc.symm (x.coefficients.aliasCoefficients l)) j

theorem nativeParticular_inactive {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
    (H : Invariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Index B N0) (n : ℕ) (hn : ¬ActualWaveRegularityData.Ordered l n) (j : ℤ)
    {z : ActualParticularStageControls.Native}
    (hz : z ∈ ActualWaveRegularity.nativeDomain ActualWaveRegularity.particularChart
      ActualPrimary.standardRegion) :
    (nativeParticularData x l j).common.amplitude n =ᶠ[𝓝 z] fun _ => 0 := by
  have hp : z.1.1 ∈ ActualCarrierTransport.parameterDomain := hz.1
  apply ActualCycleAssembly.common_raw_zero_germ_of_factorization l
    (ActualCoreSupport.refinedCarrier l) (ActualCycleAssembly.refinedSlowCore l)
    (ActualCoreSupport.refinedCarrier_closed l) (ActualCycleAssembly.refined_carrier_factorization
        hN l)
    (ActualPrimary.commonContext B) x.state (x.coefficients.blocks l)
    (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l) (H.inputSupport l) j n hp
  intro hs
  have hc := (ActualCycleAssembly.refined_carrier_factorization hN l n z.1.1 hp z.2).mpr hs
  exact hn (ActualCycleParameters.activeLabel_index n l (core_active l n hp hc))

section Factory
variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
local notation "p" => ActualCycleParameters.fixedParameters B N0
local notation "c" => ActualPrimary.commonContext B
local notation "v" => x.coefficients
local notation "u" => x.state

theorem waveData_of_particular (H : Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (hσ : 1 / 5 ≤ σ)
    (P : ActualParticularCycleData.Data x σ) :
    CorrectionAnalyticStep.WaveData G p v c u ActualInitialization.envelope
      ActualCoreSupport.refinedCarrier σ κ := by
  let d := particular_inputs H hN P.amplitude P.field P.periodic P.support
  have first := ActualParticularMeanGain.postParticular_gain H d hσ
  have hb := signed_block_bounds first
  exact {
    carrier := ActualCycleParameters.invariant_fixedParameters_signed_carrier H
    particular := P.amplitude
    tangent := hb.1
    curl := hb.2.2.2.1
    particularPressure := P.pressure
    signedPressure := hb.2.2.1
    particularSmooth := P.coefficients
    signedSmooth := signed_coefficients_smooth first
    particularPressureSmooth := P.pressureCoefficients
    signedPressureSmooth := signed_pressure_coefficients_smooth first
    particularGaussianSmooth := P.gaussianCoefficients
    signedGaussianSmooth := signed_gaussian_coefficients_smooth first
    particularSolenoidal := P.solenoidal
    signedSolenoidal := signed_solenoidal first
    particularSupport := ActualCycleAssembly.cycle_refined_particular_inputSupport hN x c
        H.inputSupport
    signedSupport := signed_inputSupport
    particularGaussian := P.gaussian
    signedGaussian := signed_gaussian_bounds first
    particularField := P.field
    signedField := signed_field_smooth first
    particularPressureField := P.pressureField
    signedPressureField := signed_pressure_field_smooth first
    particularPeriodic := P.periodic
    signedPeriodic := signed_field_periodic
    particularRadialSupport := P.support
    signedRadialSupport := signed_field_support
    tangentField := signed_tangent_field_smooth first
    tangentPeriodic := signed_tangent_field_periodic
    tangentRadialSupport := signed_tangent_field_support
    particularLinear := P.linear
    signedLinear := signed_linear_bounds H first }

/-- Step data of particular, given by `stepDataOfWaves H hN hσ hl (waveData_of_particular H hN
hσ P)`. -/
noncomputable def stepDataOfParticular (H : Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (hσ : 1 / 5 ≤ σ)
    (hl : (v).labels = ActualPrimary.activeLabels ActualPrimary.standardRegion B N0)
    (P : ActualParticularCycleData.Data x σ) :
    CorrectionAnalyticStep.StepData G ActualPrimary.h (CommonWindow.index ActualPrimary.h)
      ActualInitialization.axial
      (fun l => ActualParticularStageControls.canonicalParameters (l.2,l.1))
      ActualSignedStageControls.parameters ActualPrimary.rankData c x
      ActualInitialization.tangentBlock ActualInitialization.envelope
      ActualCoreSupport.refinedCarrier (staticData B) H hσ :=
  stepDataOfWaves H hN hσ hl (waveData_of_particular H hN hσ P)

theorem stepResult_of_particular (H : Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (hσ : 1 / 5 ≤ σ)
    (hl : (v).labels = ActualPrimary.activeLabels ActualPrimary.standardRegion B N0)
    (P : ActualParticularCycleData.Data x σ) :
    CorrectionAnalyticStep.StepResult G ActualPrimary.h (CommonWindow.index ActualPrimary.h)
      ActualInitialization.axial
      (fun l => ActualParticularStageControls.canonicalParameters (l.2,l.1))
      ActualSignedStageControls.parameters ActualPrimary.rankData c x
      ActualInitialization.tangentBlock ActualInitialization.envelope
      ActualCoreSupport.refinedCarrier (σ := σ) («κ» := κ) :=
  CorrectionAnalyticStep.step _ _ _ _ _ _ _ _ _ _ _ _
    (staticData B) H hσ kappa_small (stepDataOfParticular H hN hσ hl P)

theorem afterTemporal_debt_of_particular (H : Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (hσ : 1 / 5 ≤ σ)
    (hl : (v).labels = ActualPrimary.activeLabels ActualPrimary.standardRegion B N0)
    (P : ActualParticularCycleData.Data x σ) :
    UnweightedClass ActualInitialization.slowStrip (1+σ-2*κ)
      (debt c (ActualIntermediateDebtBounds.postTemporal x)) :=
  ActualIntermediateDebtBounds.afterTemporal_debt_from_stepData
    (staticData B) H hσ (P.inputs H hN) (stepDataOfParticular H hN hσ hl P)

end Factory

/-- The actual run retains analytic bounds, full chart coherence, and
individual torus periods as distinct, proved invariants. -/
structure RunInvariant {B N0 : ℕ} (σ : ℝ) (x : CycleState (Index B N0)) : Prop where
  analytic : Invariant σ x
  coherent : ActualCycleCoherence.Coherent x
  periodic : ActualCyclePeriodicity.Periodic x

theorem initial_runInvariant (B N0 : ℕ) :
    RunInvariant (ActualIterationLedger.sigma 0) (state B N0 0) where
  analytic := by simpa only [ActualIterationLedger.sigma_zero] using initial_invariant B N0
  coherent := ActualCycleCoherence.initial B N0
  periodic := ActualCyclePeriodicity.initial B N0

theorem coherent_core_cover {B N0 : ℕ} {x : CycleState (Index B N0)}
    (C : ActualCycleCoherence.Coherent x) :
    ∀ l n z, z ∈ ActualInitialization.geometry.domain →
      z ∈ ActualCoreSupport.refinedCarrier l n → l ∈ x.coefficients.labels n := by
  intro l n z hz hc
  rw [C.labels]
  exact core_active l n hz hc

theorem wave_transport_of_particular {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
    (R : RunInvariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (hσ : 1 / 5 ≤ σ) (P : ActualParticularCycleData.Data x σ)
    (n m k : ℕ)
    (hi : CommonWindow.index ActualPrimary.h n + k = CommonWindow.index ActualPrimary.h m) :
    CycleStateCoherence.CycleWavesOn ActualCycleCoherence.geometry
      (ActualCycleParameters.fixedParameters B N0) x.coefficients
      (ActualPrimary.commonContext B) x.state (ActualInitialCoherence.overlap n m) n m k :=
  ActualCycleCoherence.waves R.analytic (waveData_of_particular R.analytic hN hσ P)
    R.coherent (coherent_core_cover R.coherent) ActualCoreSupport.refinedCarrier_closed
    (fun _ _ => Subset.rfl) n m k hi

theorem next_runInvariant_of_particular {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
    (R : RunInvariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (hσ : 1 / 5 ≤ σ) (P : ActualParticularCycleData.Data x σ) :
    RunInvariant (σ+1/10)
      (x.step (ActualCycleParameters.fixedParameters B N0) (ActualPrimary.commonContext B)) where
  analytic := (stepResult_of_particular R.analytic hN hσ R.coherent.labels P).invariant
  coherent := ActualCycleCoherence.step R.analytic (waveData_of_particular R.analytic hN hσ P)
    R.coherent (coherent_core_cover R.coherent) ActualCoreSupport.refinedCarrier_closed
    (fun _ _ => Subset.rfl)
  periodic := ActualCyclePeriodicity.step R.analytic R.periodic

theorem particularData {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
    (R : RunInvariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (hσ : 1 / 5 ≤ σ) : ActualParticularCycleData.Data x σ :=
  ActualParticularCycleData.actual_data R.analytic R.periodic hN hσ

theorem next_runInvariant {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
    (R : RunInvariant σ x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (hσ : 1 / 5 ≤ σ) :
    RunInvariant (σ+1/10)
      (x.step (ActualCycleParameters.fixedParameters B N0) (ActualPrimary.commonContext B)) :=
  next_runInvariant_of_particular R hN hσ (particularData R hN hσ)

/-- Every stage belongs to the same fixed construction, with no wave,
regularity, covariance, or periodicity output supplied as an assumption. -/
theorem state_runInvariant (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    RunInvariant (ActualIterationLedger.sigma j) (state B N0 j) := by
  induction j with
  | zero => exact initial_runInvariant B N0
  | succ j ih =>
      rw [ActualIterationLedger.sigma_succ, state_succ]
      exact next_runInvariant ih hN (ActualIterationLedger.sigma_admissible j)

theorem state_invariant (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    Invariant (ActualIterationLedger.sigma j) (state B N0 j) :=
  (state_runInvariant B N0 hN j).analytic

theorem state_coherent (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    ActualCycleCoherence.Coherent (state B N0 j) :=
  (state_runInvariant B N0 hN j).coherent

theorem state_periodic (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    ActualCyclePeriodicity.Periodic (state B N0 j) :=
  (state_runInvariant B N0 hN j).periodic

theorem state_particularData (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    ActualParticularCycleData.Data (state B N0 j) (ActualIterationLedger.sigma j) :=
  particularData (state_runInvariant B N0 hN j) hN (ActualIterationLedger.sigma_admissible j)

theorem state_particularInputs (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    ActualParticularMeanGain.Inputs (state B N0 j) (ActualIterationLedger.sigma j) :=
  (state_particularData B N0 hN j).inputs (state_invariant B N0 hN j) hN

theorem state_waveData (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    CorrectionAnalyticStep.WaveData ActualInitialization.geometry
      (ActualCycleParameters.fixedParameters B N0) (state B N0 j).coefficients
      (ActualPrimary.commonContext B) (state B N0 j).state ActualInitialization.envelope
      ActualCoreSupport.refinedCarrier (ActualIterationLedger.sigma j) ChartScales.kappa :=
  waveData_of_particular (state_invariant B N0 hN j) hN
    (ActualIterationLedger.sigma_admissible j) (state_particularData B N0 hN j)

/-- State step data, constructed using `stepDataOfParticular`. -/
noncomputable def stateStepData (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    CorrectionAnalyticStep.StepData ActualInitialization.geometry ActualPrimary.h
      (CommonWindow.index ActualPrimary.h) ActualInitialization.axial
      (fun l => ActualParticularStageControls.canonicalParameters (l.2,l.1))
      ActualSignedStageControls.parameters ActualPrimary.rankData (ActualPrimary.commonContext B)
      (state B N0 j) ActualInitialization.tangentBlock ActualInitialization.envelope
      ActualCoreSupport.refinedCarrier (staticData B) (state_invariant B N0 hN j)
      (ActualIterationLedger.sigma_admissible j) :=
  stepDataOfParticular (state_invariant B N0 hN j) hN
    (ActualIterationLedger.sigma_admissible j) (state_labels B N0 j)
    (state_particularData B N0 hN j)

theorem state_result (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    CorrectionAnalyticStep.StepResult ActualInitialization.geometry ActualPrimary.h
      (CommonWindow.index ActualPrimary.h) ActualInitialization.axial
      (fun l => ActualParticularStageControls.canonicalParameters (l.2,l.1))
      ActualSignedStageControls.parameters ActualPrimary.rankData (ActualPrimary.commonContext B)
      (state B N0 j) ActualInitialization.tangentBlock ActualInitialization.envelope
      ActualCoreSupport.refinedCarrier (σ := ActualIterationLedger.sigma j) («κ» :=
          ChartScales.kappa) :=
  stepResult_of_particular (state_invariant B N0 hN j) hN
    (ActualIterationLedger.sigma_admissible j) (state_labels B N0 j)
    (state_particularData B N0 hN j)

theorem state_afterTemporal_debt (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    UnweightedClass ActualInitialization.slowStrip
      (1+ActualIterationLedger.sigma j-2*ChartScales.kappa)
      (debt (ActualPrimary.commonContext B)
        (ActualIntermediateDebtBounds.postTemporal (state B N0 j))) :=
  afterTemporal_debt_of_particular (state_invariant B N0 hN j) hN
    (ActualIterationLedger.sigma_admissible j) (state_labels B N0 j)
    (state_particularData B N0 hN j)

theorem state_wave_transport (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j n m k : ℕ)
    (hi : CommonWindow.index ActualPrimary.h n + k = CommonWindow.index ActualPrimary.h m) :
    CycleStateCoherence.CycleWavesOn ActualCycleCoherence.geometry
      (ActualCycleParameters.fixedParameters B N0) (state B N0 j).coefficients
      (ActualPrimary.commonContext B) (state B N0 j).state
      (ActualInitialCoherence.overlap n m) n m k :=
  wave_transport_of_particular (state_runInvariant B N0 hN j) hN
    (ActualIterationLedger.sigma_admissible j) (state_particularData B N0 hN j) n m k hi

theorem state_covariance_moving (B N0 : ℕ)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℕ) :
    (∀ i k, GaugeMomentBalances.MovingField ActualPrimary.standardRegion
      ActualInitialization.patch.a ActualInitialization.patch.b
      (SignedMeanGain.covarianceIncrement (state B N0 j).state.oscillation
        ((ActualCycleParameters.fixedParameters B N0).particularVelocity (state B N0 j).coefficients
          (ActualPrimary.commonContext B) (state B N0 j).state) i k)) ∧
    (∀ i k, GaugeMomentBalances.MovingField ActualPrimary.standardRegion
      ActualInitialization.patch.a ActualInitialization.patch.b
      (SignedMeanGain.covarianceIncrement
        ((ActualCycleParameters.fixedParameters B N0).afterParticular (state B N0 j).coefficients
          (ActualPrimary.commonContext B) (state B N0 j).state).oscillation
        ((ActualCycleParameters.fixedParameters B N0).signedVelocity (state B N0 j).coefficients
          (ActualPrimary.commonContext B) (state B N0 j).state) i k)) :=
  (state_waveData B N0 hN j).covariance_moving (state_invariant B N0 hN j).oscillationSmooth
    (state_invariant B N0 hN j).oscillationPeriodic

end NavierStokes.ActualCyclePreservation

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleParameters
import LeanPool.NavierStokesAndEuler.NavierStokes.SignedCrossDefectClass

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

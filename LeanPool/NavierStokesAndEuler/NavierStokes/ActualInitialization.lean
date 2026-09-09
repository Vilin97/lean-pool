/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualInitialMeanEquation
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPrimaryDynamics
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualInitialExcluded
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualInitialCoherence
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualInitialMean
public import LeanPool.NavierStokesAndEuler.NavierStokes.GaugeRadialResidualBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectionInitialization
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualBaseResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPrimaryBounds

@[expose] public section

/-!
# The actual initialized correction state

This consumer uses the single primary family selected by
`CorrectionInitialization.ActualPrimary`, retaining its exact pressure,
Gaussian errors and common-cover chart representations.
-/

noncomputable section

namespace NavierStokes.ActualInitialization

open Set Function Filter CorrectionState CorrectionInitialization
open scoped ContDiff Topology BigOperators

abbrev Point := LocalSignedRequest.Point
abbrev Index (B N0 : ℕ) := ActualPrimary.Label B N0 × Fin 2

variable {B N0 : ℕ}

noncomputable def primaryPiece (l : Index B N0) : PrimaryPiece (Point × ℝ) :=
  ActualPrimary.piece ActualPrimary.standardRegion l.2 l.1

noncomputable def phase (l : Index B N0) (n : ℕ) (x : Point) : ℝ :=
  (primaryPiece l).coefficients.phase n (x, 0)

noncomputable def angularMode (l : Index B N0) (_n : ℕ) : ℤ :=
  PrimaryGeometryAssembly.angularMode ActualPrimary.certificate ActualPrimary.modulation
    (ActualPrimary.choice B N0).prepared l.2 l.1

noncomputable def primaryBlock (l : Index B N0) : HarmonicBlock Point :=
  (primaryPiece l).harmonicBlock (phase l) (angularMode l)

noncomputable def tangentBlock (l : Index B N0) : HarmonicBlock Point :=
  (primaryPiece l).tangentBlock (phase l) (angularMode l)

noncomputable def curlBlock (l : Index B N0) : HarmonicBlock Point :=
  (primaryPiece l).differenceBlock (phase l) (angularMode l)

noncomputable def gaussianBlock (l : Index B N0) : HarmonicBlock Point :=
  (primaryPiece l).excludedBlock (phase l) (angularMode l)

theorem angularMode_ne_zero (l : Index B N0) (n : ℕ) : angularMode l n ≠ 0 :=
  PrimaryGeometryAssembly.angularMode_ne_zero ActualPrimary.certificate ActualPrimary.modulation
    (ActualPrimary.choice B N0).prepared l.2 l.1

theorem phase_split (l : Index B N0) (n : ℕ) (x : Point) (theta : ℝ) :
    (primaryPiece l).coefficients.frequency n * (primaryPiece l).coefficients.phase n (x, theta) =
      (primaryPiece l).coefficients.frequency n * phase l n x + (angularMode l n : ℝ) * theta := by
  change (ActualPrimary.chartCoefficients l.2 l.1).frequency n * (ActualPrimary.chartCoefficients
    l.2 l.1).phase n (x, theta) =
    (ActualPrimary.chartCoefficients l.2 l.1).frequency n * (ActualPrimary.chartCoefficients l.2
      l.1).phase n (x, 0) + _
  rw [ActualPrimary.chartCoefficients_phase, ActualPrimary.chartCoefficients_phase]
  simp only [ActualPrimary.absolutePhase, angularMode, mul_zero, zero_add]
  ring

theorem cutoff_smooth (l : Index B N0) (n : ℕ) : ContDiff ℝ ∞ ((primaryPiece l).cutoff n) :=
  (ActualPrimary.periodicGaussian_smooth l.2 l.1).comp ((ActualPrimary.toAbsolute_smooth
    n).snd.comp contDiff_fst)

theorem amplitude_angle (l : Index B N0) :
    ErrorHarmonics.AngleIndependent (primaryPiece l).coefficients.amplitude := fun _ _ _ => rfl

theorem cutoff_angle (l : Index B N0) :
    ErrorHarmonics.AngleIndependent (primaryPiece l).cutoff := fun _ _ _ => rfl

theorem exact_amplitude_angle (l : Index B N0) :
    ErrorHarmonics.AngleIndependent (primaryPiece l).exactCoefficients.amplitude := by
  intro n x theta
  exact CopyAngularInvariance.invariant_eq_zeroSlice
    ((ActualPrimary.chartCoefficients_angular l.2 l.1).corrected_amplitude
      (BaseContextAssembly.nativeStrip ActualPrimary.nominal ActualPrimary.standardRegion)
        (ActualPrimary.commonContext B) n) x theta

theorem exact_pressure_angle (l : Index B N0) :
    ErrorHarmonics.AngleIndependent (primaryPiece l).exactCoefficients.pressure := by
  intro n x theta
  exact CopyAngularInvariance.invariant_eq_zeroSlice
    ((ActualPrimary.chartCoefficients_angular l.2 l.1).corrected_pressure
      (BaseContextAssembly.nativeStrip ActualPrimary.nominal ActualPrimary.standardRegion)
        (ActualPrimary.commonContext B) n) x theta

theorem tangent_amplitude_angle (l : Index B N0) :
    ErrorHarmonics.AngleIndependent
      ((primaryPiece l).coefficients.withCutoff (primaryPiece l).cutoff).amplitude := fun _ _ _ =>
        rfl

theorem primaryBlock_represents (l : Index B N0) :
    (primaryBlock l).oscillation = (primaryPiece l).velocity ∧
      (primaryBlock l).oscillatoryPressure = (primaryPiece l).pressure :=
  (primaryPiece l).harmonicBlock_represents (phase l) (angularMode l)
    (exact_amplitude_angle l) (exact_pressure_angle l) (phase_split l)

theorem tangentBlock_represents (l : Index B N0) :
    (tangentBlock l).oscillation = (primaryPiece l).tangentVelocity := by
  funext n x i
  exact PrimaryHarmonics.block_velocity_represents
    ((primaryPiece l).coefficients.withCutoff (primaryPiece l).cutoff)
    (phase l) (angularMode l) (tangent_amplitude_angle l) (phase_split l) n x i

theorem curlBlock_represents (l : Index B N0) :
    (curlBlock l).oscillation = (primaryPiece l).velocity - (primaryPiece l).tangentVelocity :=
  (primaryPiece l).differenceBlock_represents (phase l) (angularMode l)
    (exact_amplitude_angle l) (tangent_amplitude_angle l) (phase_split l)

theorem gaussianBlock_represents (l : Index B N0) :
    (gaussianBlock l).oscillation = (primaryPiece l).excluded :=
  (primaryPiece l).excludedBlock_represents (phase l) (angularMode l)
    (cutoff_smooth l) (cutoff_angle l) (amplitude_angle l) (phase_split l)

theorem gaussian_mean_zero (l : Index B N0) :
    CorrectionStep.angularMeanVector (primaryPiece l).excluded = 0 :=
  (primaryPiece l).excluded_mean_zero (phase l) (angularMode l) (angularMode_ne_zero l)
    (cutoff_smooth l) (cutoff_angle l) (amplitude_angle l) (phase_split l)

theorem gaussian_angularContinuous (l : Index B N0) :
    CorrectionStep.AngularContinuous (primaryPiece l).excluded :=
  (primaryPiece l).excluded_angularContinuous (phase l) (angularMode l)
    (cutoff_smooth l) (cutoff_angle l) (amplitude_angle l) (phase_split l)

theorem primaryBlock_band (l : Index B N0) : (primaryBlock l).BandLimited 1 :=
  PrimaryHarmonics.block_band _ _ _

theorem gaussianBlock_band (l : Index B N0) : (gaussianBlock l).BandLimited 1 :=
  ErrorHarmonics.gaussianBlock_band _ _ _ _ 1 _ _ _

noncomputable def coefficients (B N0 : ℕ) : CorrectionStep.CycleCoefficients (Index B N0) where
  labels := ActualPrimary.activeLabels ActualPrimary.standardRegion B N0
  blocks := primaryBlock
  gaussian l := (gaussianBlock l).velocity
  aliasCoefficients _ := 0
  residualBand := 2

theorem coefficients_band (B N0 : ℕ) : CorrectionStep.CoefficientBands (coefficients B N0) := by
  constructor
  · intro l
    exact ⟨fun n i => ((primaryBlock_band l).1 n i).mono (by norm_num [coefficients]),
      fun n => ((primaryBlock_band l).2 n).mono (by norm_num [coefficients])⟩
  · intro l n i
    exact ((gaussianBlock_band l).1 n i).mono (by norm_num [coefficients])
  · intro l n i j hj
    simp [coefficients] at hj

theorem gaussian_coefficientField (l : Index B N0) :
    CorrectionStep.coefficientField (primaryBlock l) (gaussianBlock l).velocity =
      (primaryPiece l).excluded := by
  rw [← gaussianBlock_represents]
  rfl


noncomputable def baseError (B : ℕ) : Oscillation Point :=
  ActualBaseResidual.baseError ActualPrimary.certificate ActualPrimary.modulation
    ActualPrimary.upper B

noncomputable def sourceState (B N0 : ℕ) : State Point :=
  bandSeed (coefficients B N0).labels primaryPiece (baseError B)

noncomputable def primaryState (B N0 : ℕ) : State Point :=
  VariableGaugeMean.reconstructState ActualPrimary.commonGauge (ActualPrimary.commonContext B)
    (sourceState B N0)

noncomputable def axial : TorusInverse.Plane × TorusInverse.Plane := ((0, 1), 0)

noncomputable def temporalState (B N0 : ℕ) : State Point :=
  VariableGaugeMean.temporalStageState ActualPrimary.commonGauge ActualPrimary.h
    (CommonWindow.index ActualPrimary.h) axial (ActualPrimary.commonContext B) (primaryState B N0)

noncomputable def rankState (B N0 : ℕ) : State Point :=
  VariableGaugeMean.rankStageState ActualPrimary.commonGauge ActualPrimary.rankData axial
    (ActualPrimary.commonContext B) (temporalState B N0)

noncomputable def initialState (B N0 : ℕ) : State Point :=
  GaugeInitialization.retainPressureAlias ActualPrimary.commonGauge (ActualPrimary.commonContext B)
    (rankState B N0)

noncomputable def initialAlias (B N0 : ℕ) : CorrectionStep.AxisymmetricAlias :=
  fun n x i => VariableGaugeMean.temporalAliasState ActualPrimary.commonGauge ActualPrimary.h
      (CommonWindow.index ActualPrimary.h) (ActualPrimary.commonContext B) (primaryState B N0) n
        (x,0) i +
    VariableGaugeMean.pressureAliasState ActualPrimary.commonGauge (ActualPrimary.commonContext B)
      (rankState B N0) n (x,0) i

/-- The initial state and its actual harmonic data are constructed together;
all later iterations retain these physical labels. -/
noncomputable def initialCycleState (B N0 : ℕ) : CorrectionStep.CycleState (Index B N0) where
  state := initialState B N0
  coefficients := coefficients B N0
  axisymmetricAlias := initialAlias B N0

theorem initialState_eq_bands (B N0 : ℕ) :
    initialState B N0 = GaugeInitialization.initializedBands ActualPrimary.commonGauge
      ActualPrimary.rankData
      ActualPrimary.h (CommonWindow.index ActualPrimary.h) axial (ActualPrimary.commonContext B)
      (coefficients B N0).labels primaryPiece (baseError B) := rfl

theorem initialState_error_components (B N0 : ℕ) :
    (initialState B N0).errors.base = baseError B ∧
    (initialState B N0).errors.gaussian =
      LabelSumBounds.fieldSum (coefficients B N0).labels (fun l => (primaryPiece l).excluded) ∧
    (initialState B N0).errors.aliasError = fun n x i => initialAlias B N0 n x.1 i := by
  have he := GaugeInitialization.initializedBands_error_components ActualPrimary.commonGauge
    ActualPrimary.rankData ActualPrimary.h (CommonWindow.index ActualPrimary.h) axial
    (ActualPrimary.commonContext B) (coefficients B N0).labels primaryPiece (baseError B)
  refine ⟨he.1, he.2.1, ?_⟩
  have ha := he.2.2
  simp only [initialAlias, VariableGaugeMean.temporalAliasState,
    VariableGaugeMean.pressureAliasState] at ha ⊢
  exact ha

theorem initialCycleState_represents (B N0 : ℕ) :
    CorrectionStep.CycleRepresentation (initialCycleState B N0).coefficients
      (initialCycleState B N0).state (initialCycleState B N0).axisymmetricAlias := by
  constructor
  · intro n x i
    have he := congrArg (fun f : Oscillation Point => f n x i)
      (GaugeInitialization.initializedBands_oscillation ActualPrimary.commonGauge
        ActualPrimary.rankData
        ActualPrimary.h (CommonWindow.index ActualPrimary.h) axial (ActualPrimary.commonContext B)
        (coefficients B N0).labels primaryPiece (baseError B))
    change (initialState B N0).oscillation n x i = _ at he
    change (initialState B N0).oscillation n x i = _
    rw [he]
    change (∑ l ∈ (coefficients B N0).labels n, (primaryPiece l).velocity n x i) = _
    apply Finset.sum_congr rfl
    intro l hl
    exact congrArg (fun f : Oscillation Point => f n x i) (primaryBlock_represents l).1.symm
  · intro n x
    change (initialState B N0).oscillatoryPressure n x = _
    have he : (initialState B N0).oscillatoryPressure n x =
        ∑ l ∈ (coefficients B N0).labels n, (primaryPiece l).pressure n x := by
      simp [initialState, rankState, temporalState, primaryState, sourceState, bandSeed,
        GaugeInitialization.retainPressureAlias, VariableGaugeMean.rankStageState,
        VariableGaugeMean.temporalStageState, VariableGaugeMean.reconstructState,
          State.addIncrement]
    rw [he]
    apply Finset.sum_congr rfl
    intro l hl
    exact congrArg (fun f => f n x) (primaryBlock_represents l).2.symm
  · intro n x i
    change (initialState B N0).errors.gaussian n x i = _
    rw [(initialState_error_components B N0).2.1]
    change (∑ l ∈ (coefficients B N0).labels n, (primaryPiece l).excluded n x i) = _
    apply Finset.sum_congr rfl
    intro l hl
    exact congrArg (fun f : Oscillation Point => f n x i) (gaussian_coefficientField l).symm
  · intro n x i
    change (initialState B N0).errors.aliasError n x i = _
    rw [(initialState_error_components B N0).2.2]
    simp [initialCycleState, coefficients, CorrectionStep.coefficientField, HarmonicFields.field]

end NavierStokes.ActualInitialization

namespace NavierStokes.ActualInitialization

open Set Function Filter CorrectionState CorrectionInitialization
open scoped ContDiff Topology BigOperators

variable {B N0 : ℕ}

theorem primaryBlock_zeroMode (l : Index B N0) : HarmonicWaveInteraction.ZeroMode (primaryBlock l)
  :=
  (SignedWaveUpdate.coefficientBlock_zero_coefficient
    (primaryPiece l).coefficients.frequency (phase l) (angularMode l)
    (fun n x => (primaryPiece l).exactCoefficients.amplitude n (x,0))
    (fun n x => (primaryPiece l).exactCoefficients.pressure n (x,0))).1

theorem primaryBlock_symmetric (l : Index B N0) (n : ℕ) (i : Fin 3) :
    HarmonicFields.ConjugateSymmetric ((primaryBlock l).velocity n i) :=
  ErrorHarmonics.conjugatePair_symmetric 1 _

theorem sourceState_mean (B N0 : ℕ) : (sourceState B N0).mean = ⟨0,0,0⟩ := rfl

theorem initialState_oscillation (B N0 : ℕ) :
    (initialState B N0).oscillation = (sourceState B N0).oscillation :=
  GaugeInitialization.initializedBands_oscillation ActualPrimary.commonGauge ActualPrimary.rankData
    ActualPrimary.h (CommonWindow.index ActualPrimary.h) axial (ActualPrimary.commonContext B)
    (coefficients B N0).labels primaryPiece (baseError B)

theorem initialState_covariance (B N0 : ℕ) :
    (initialState B N0).covariance = (sourceState B N0).covariance := by
  unfold State.covariance
  rw [initialState_oscillation]

theorem initialState_reconstructed (B N0 : ℕ) :
    VariableGaugeMean.reconstructState ActualPrimary.commonGauge (ActualPrimary.commonContext B)
      (initialState B N0) = initialState B N0 := rfl

/-- The actual nonconstant residual coefficients supplied to the first
particular solve. The separate axisymmetric alias is removed only by
the angular nonconstant projection. -/
noncomputable def initialResidualBlock (l : Index B N0) : HarmonicBlock Point :=
  HarmonicResidual.residualBlock (ActualPrimary.commonContext B) (initialState B N0)
    (primaryBlock l) (gaussianBlock l).velocity 0

theorem initialResidualBlock_band (l : Index B N0) : (initialResidualBlock l).BandLimited 2 := by
  have hG : ∀ n i, HarmonicFields.BandLimited ((gaussianBlock l).velocity n i) 1 :=
    (gaussianBlock_band l).1
  have hA : ∀ n i, HarmonicFields.BandLimited
      ((0 : HarmonicResidual.BlockCoefficients Point) n i) 1 :=
    fun _ _ => HarmonicResidual.band_zero 1
  exact HarmonicResidual.residualBlock_band (ActualPrimary.commonContext B) (initialState B N0)
    (primaryBlock l) (gaussianBlock l).velocity 0 (primaryBlock_band l) hG hA

theorem initialResidualBlock_zeroMode (l : Index B N0) :
    HarmonicWaveInteraction.ZeroMode (initialResidualBlock l) :=
  HarmonicResidual.residualBlock_zero_mode (ActualPrimary.commonContext B) (initialState B N0)
    (primaryBlock l) (gaussianBlock l).velocity 0

theorem initialResidualBlock_symmetric (l : Index B N0) (n : ℕ) (i : Fin 3) :
    HarmonicFields.ConjugateSymmetric ((initialResidualBlock l).velocity n i) :=
  HarmonicResidual.residualBlock_conjugate (ActualPrimary.commonContext B) (initialState B N0)
    (primaryBlock l) (gaussianBlock l).velocity 0 n i

end NavierStokes.ActualInitialization

namespace NavierStokes.ActualInitialization

open Set Filter Function WeightedClasses CorrectionState
open HarmonicMeanInteraction HarmonicWaveInteraction UniformHarmonicInteraction
open scoped ContDiff Topology

/-- The actual nonlinear coefficient of a mean-zero state is its linear
coefficient plus the solenoidal self-transport. Constants remain uniform
before the spatial label. -/
theorem zeroMean_residual_uniform
    {D : Type} {ι : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {s : StripData D} {P : ι → ℕ → D → ℝ} {κ α γ : ℝ}
    (c : Context D) (ho : MeanIncrementBounds.OperatorBounds s c.operators κ)
    (hR : ∀ x ∈ s.domain, 0 < c.operators.radius x)
    (u : State D) (hm : u.mean = ⟨0,0,0⟩)
    (b : ι → HarmonicBlock D) (G A : ι → HarmonicResidual.BlockCoefficients D)
    (hb : UniformVelocity s P α b)
    (hzero : ∀ l, ZeroMode (b l)) {M : ℕ}
    (hband : ∀ l, (b l).BandLimited M)
    (hphase : ∀ l n, ContDiffOn ℝ ∞ ((b l).phase n) s.domain)
    (hk : ∀ l n, (b l).frequency n ≠ 0)
    (hdiv : ∀ l, ModeSolenoidal s c (b l))
    (hP0 : ∀ l n x, x ∈ s.domain → 0 ≤ P l n x)
    (hP1 : ∀ l n x, x ∈ s.domain → P l n x ≤ 1)
    (hA : ∀ l n i j, j ≠ 0 → A l n i j = 0)
    (hlinear : UniformVelocity s P γ (fun l => linearGoodBlock c (b l) (b l) (G l)))
    (hγ : γ ≤ α + α - κ) :
    UniformVelocity s P γ (fun l => HarmonicResidual.residualBlock c u (b l) (G l) (A l)) := by
  intro i j hj
  have ht (m : ℤ) := (transport_uniform c ho hR hb hb hzero hzero hband
    hphase hk hdiv hP0 hP1 m i).mono_exponent hγ
  have hr := LabelSumBounds.uniform_realCoefficients
    (fun l n => HarmonicResidual.transport (HarmonicResidual.contextFrame c n)
      ((b l).frequency n) ((b l).phase n) ((b l).angularFrequency n)
      (blockAmplitude (b l) n) (blockAmplitude (b l) n) i) ht j
  apply ((hlinear i j hj).add hr).congr
  intro l n x hx
  have hmean : HarmonicResidual.stateMean u n = 0 := by
    funext y k
    fin_cases k <;> simp [HarmonicResidual.stateMean, hm]
  change HarmonicResidual.nonconstant
    (HarmonicResidual.realCoefficients (linearCoefficients c (b l) (b l) n i - G l n i)) j x +
      HarmonicResidual.realCoefficients
        (HarmonicResidual.transport (HarmonicResidual.contextFrame c n)
          ((b l).frequency n) ((b l).phase n) ((b l).angularFrequency n)
          (blockAmplitude (b l) n) (blockAmplitude (b l) n) i) j x =
    HarmonicResidual.nonconstant
      ((HarmonicResidual.ofBlock (b l) (G l) (A l) n).residualCoefficients
        (HarmonicResidual.contextFrame c n) (HarmonicResidual.contextBase c n)
        (HarmonicResidual.stateMean u n) i) j x
  rw [nonconstant_apply_of_ne _ hj, nonconstant_apply_of_ne _ hj, hmean,
    HarmonicResidual.LabelData.residualCoefficients]
  simp only [add_zero]
  let L := linearCoefficients c (b l) (b l) n i
  let T := HarmonicResidual.transport (HarmonicResidual.contextFrame c n)
    ((b l).frequency n) ((b l).phase n) ((b l).angularFrequency n)
    (blockAmplitude (b l) n) (blockAmplitude (b l) n) i
  change HarmonicResidual.realCoefficients (L - G l n i) j x +
    HarmonicResidual.realCoefficients T j x =
      HarmonicResidual.realCoefficients (L + T - G l n i - A l n i) j x
  simp only [HarmonicResidual.realCoefficients_apply, coeff_add, coeff_sub,
    hA l n i j hj, hA l n i (-j) (neg_ne_zero.mpr hj),
    Pi.zero_apply, map_sub, map_add, sub_zero]
  ring

end NavierStokes.ActualInitialization

namespace NavierStokes.ActualInitialization

open Set Function Filter CorrectionState CorrectionInitialization WeightedClasses
open scoped ContDiff Topology BigOperators

noncomputable def strip : StripData Point :=
  BaseContextAssembly.nativeStrip ActualPrimary.nominal ActualPrimary.standardRegion

noncomputable def slowStrip : StripData TorusInverse.Plane :=
  PhysicalMeanDomain.localSlowStripData ActualPrimary.standardRegion.carrier
    ActualPrimary.standardRegion.isOpen (ChartScales.epsilon ActualPrimary.h)
    BaseContextAssembly.slowScale (ChartScales.epsilon_pos ActualPrimary.h)
    (ChartScales.epsilon_le_one ActualPrimary.h ActualPrimary.outgoing.data.h_pos.le)
    BaseContextAssembly.one_le_slowScale

noncomputable def envelope {B N0 : ℕ} (l : Index B N0) : ℕ → Point → ℝ :=
  ActualPrimaryBounds.meanEnvelope (l.2,l.1)

theorem envelope_nonneg {B N0 : ℕ} (l : Index B N0) (n : ℕ) (x : Point) :
    0 ≤ envelope l n x := ActualPrimaryBounds.fullEnvelope_nonneg _ _ _

theorem envelope_le_one {B N0 : ℕ} (l : Index B N0) (n : ℕ) (x : Point) :
    envelope l n x ≤ 1 := ActualPrimaryBounds.fullEnvelope_le_one _ _ _

theorem operators (B : ℕ) :
    MeanIncrementBounds.OperatorBounds strip (ActualPrimary.commonContext B).operators
      ChartScales.kappa :=
  CommonBaseContext.context_operator_bounds ActualPrimary.certificate ActualPrimary.modulation
    ActualPrimary.upper B ActualPrimary.standardRegion (CommonWindow.index_le_native
      ActualPrimary.h)

theorem base_bounds (B : ℕ) :
    MeanIncrementBounds.BaseBounds strip (ActualPrimary.commonContext B).base :=
  CommonBaseContext.context_base_bounds ActualPrimary.certificate ActualPrimary.modulation
    ActualPrimary.upper B ActualPrimary.standardRegion (CommonWindow.index ActualPrimary.h)

theorem radius_pos (B : ℕ) (x : Point) (hx : x ∈ strip.domain) :
    0 < (ActualPrimary.commonContext B).operators.radius x :=
  BaseContextAssembly.nativeStrip_radius ActualPrimary.nominal ActualPrimary.standardRegion hx

theorem strip_time (x : Point) (hx : x ∈ strip.domain) : 0 < x.2.1.1 :=
  BaseContextAssembly.nativeStrip_time ActualPrimary.nominal ActualPrimary.standardRegion hx

theorem tangent_coefficients_uniform (B N0 : ℕ) (i : Fin 3) (j : ℤ) :
    LabelSumBounds.UniformWaveClass strip envelope (1/2)
      (fun l : Index B N0 => fun n x => (tangentBlock l).velocity n i j x) :=
  (ActualPrimaryBounds.tangent_block_uniform.1 i j).reindex Prod.swap

/-- The exact curl construction retains the same pressure coefficient. -/
theorem pressure_coefficients_uniform (B N0 : ℕ) (j : ℤ) :
    LabelSumBounds.UniformWaveClass strip envelope 1
      (fun l : Index B N0 => fun n x => (primaryBlock l).pressure n j x) :=
  (ActualPrimaryBounds.tangent_block_uniform.2 j).reindex Prod.swap

end NavierStokes.ActualInitialization

namespace NavierStokes.ActualInitialization

open Set Function Filter CorrectionState CorrectionInitialization WeightedClasses
open scoped ContDiff Topology BigOperators

variable {B N0 : ℕ}

noncomputable def goodBlock (l : Index B N0) : HarmonicBlock Point :=
  SignedWaveUpdate.coefficientBlock (primaryPiece l).coefficients.frequency
    (phase l) (angularMode l) (fun n x => (primaryPiece l).linearGood n (x,0)) 0

theorem goodBlock_represents (l : Index B N0) :
    (goodBlock l).oscillation = (primaryPiece l).linearGoodField := by
  funext n x i
  change (HarmonicFields.field (ErrorHarmonics.conjugatePair 1
    (fun y => (primaryPiece l).linearGood n (y,0) i))
      ((primaryPiece l).coefficients.frequency n) (phase l n) (angularMode l n) x).re = _
  have hi : CopyAngularInvariance.Invariant ((0 : Point),1)
      (fun y => (primaryPiece l).linearGood n y i) :=
    ((ActualPrimary.chartCoefficients_angular l.2 l.1).constructedGood strip
      (ActualPrimary.commonContext B) n).component i
  have he := congrArg Complex.re (PrimaryResidualClass.pair_field_of_invariant
    ((primaryPiece l).coefficients.frequency n) (angularMode l n) hi (phase_split l n) x)
  simp only [PrimaryResidualClass.realProjection_apply, Complex.ofReal_re] at he
  exact he

theorem goodBlock_symmetric (l : Index B N0) (n : ℕ) (i : Fin 3) :
    HarmonicFields.ConjugateSymmetric ((goodBlock l).velocity n i) :=
  ErrorHarmonics.conjugatePair_symmetric 1 _

theorem exact_frame_match (l : Index B N0) :
    CorrectionStep.WaveFrameMatch (ActualPrimary.commonContext B) (primaryPiece l).strip
      (primaryPiece l).directions (primaryPiece l).exactCoefficients := by
  refine ⟨fun _ => rfl, fun _ => rfl, ?_, rfl, ?_, ?_,
    fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  · intro n
    exact PrimaryResidualClass.directions_radial (ActualPrimary.commonContext B) n
  · intro n
    exact PrimaryResidualClass.directions_axial strip (ActualPrimary.commonContext B) rfl n
  · intro n
    exact PrimaryResidualClass.directions_time strip (ActualPrimary.commonContext B) rfl n

theorem radialDirection_smooth (B n : ℕ) :
    ContDiffOn ℝ ∞ (CorrectionStep.radialDirection (ActualPrimary.commonContext B) n)
      (HarmonicResidual.liftDomain strip.domain) := by
  have hr := ((HarmonicMeanInteraction.slowGeometry (ActualPrimary.commonContext B)
    (operators B) (radius_pos B)).radial_class.smooth n)
  exact (hr.comp contDiffOn_fst (fun _ hx => hx.1)).prodMk contDiffOn_const

theorem axialDirection_smooth (B n : ℕ) :
    ContDiffOn ℝ ∞ (CorrectionStep.axialDirection (ActualPrimary.commonContext B) n)
      (HarmonicResidual.liftDomain strip.domain) := contDiffOn_const

/-- The real harmonic operator is the operator of the literal corrected
coefficient. Only regularity of those actual fields is used here. -/
theorem linearBlockField_eq_piece (l : Index B N0) (n : ℕ)
    (hphase : ContDiffOn ℝ ∞ ((primaryPiece l).coefficients.phase n)
      (HarmonicResidual.liftDomain strip.domain))
    (hv : ∀ i, ContDiffOn ℝ ∞ (fun x => (primaryPiece l).exactCoefficients.amplitude n x i)
      (HarmonicResidual.liftDomain strip.domain))
    (hp : ContDiffOn ℝ ∞ ((primaryPiece l).exactCoefficients.pressure n)
      (HarmonicResidual.liftDomain strip.domain))
    {x : Point × ℝ} (hx : x ∈ HarmonicResidual.liftDomain strip.domain) (i : Fin 3) :
    CorrectionStep.linearBlockField (ActualPrimary.commonContext B) (primaryBlock l) (primaryBlock
      l) n x i =
      (primaryPiece l).linearResidual n x i := by
  have he := CorrectionStep.linearBlockField_eq_modeResidual strip.isOpen_domain
    (ActualPrimary.commonContext B) (primaryBlock l) (primaryBlock l)
    (primaryPiece l).strip (primaryPiece l).directions (primaryPiece l).exactCoefficients
    (exact_frame_match l) n (base_bounds B).smooth
    (radialDirection_smooth B n) (axialDirection_smooth B n) hphase hv hp
    (congrFun (primaryBlock_represents l).1 n)
    (congrFun (primaryBlock_represents l).2 n) hx
  exact congrFun he i

end NavierStokes.ActualInitialization

namespace NavierStokes.ActualInitialization

open Set Filter Function WeightedClasses CorrectionState
open HarmonicMeanInteraction HarmonicWaveInteraction UniformHarmonicInteraction
open scoped ContDiff Topology

/-- The actual initialized mean changes the primary residual by a term of
order at least nine tenths.  The retained axisymmetric aliases do not enter
the nonzero harmonic coefficients. -/
theorem initial_residual_uniform_of_primary (B N0 : ℕ)
    (hprimary : UniformVelocity strip envelope (1/2) (primaryBlock (B := B) (N0 := N0)))
    (hlinear : UniformVelocity strip envelope (7/10)
      (fun l : Index B N0 => linearGoodBlock (CorrectionInitialization.ActualPrimary.commonContext
        B)
        (primaryBlock l) (primaryBlock l) (gaussianBlock l).velocity))
    (hphase : ∀ (l : Index B N0) n, ContDiffOn ℝ ∞ (phase l n) strip.domain)
    (hdiv : ∀ l : Index B N0, ModeSolenoidal strip
      (CorrectionInitialization.ActualPrimary.commonContext B) (primaryBlock l))
    {C : ℕ → Index B N0 → Set Point}
    (hNormal : ∀ i, LocalizedWaveBounds.LocalUnweighted strip C 0
      (fun n l x => slowNormal (CorrectionInitialization.ActualPrimary.commonContext B)
        (operators B) (radius_pos B) (phase l) n x i))
    (hFreq : LocalizedWaveBounds.LocalUnweighted strip C (-(1/2))
      (fun n l _ => (primaryBlock l).frequency n))
    (hAng : LocalizedWaveBounds.LocalUnweighted strip C (-(1/2))
      (fun n l _ => ((primaryBlock l).angularFrequency n : ℝ)))
    (hz : ∀ n l x, x ∈ strip.domain → x ∉ C n l →
      ∀ i j, j ≠ 0 → (primaryBlock l).velocity n i j =ᶠ[𝓝 x] fun _ => 0)
    (hmean : CorrectionState.CumulativeBounds strip (initialState B N0)) :
    UniformVelocity strip envelope (7/10) (initialResidualBlock (B := B) (N0 := N0)) := by
  have hzero : UniformVelocity strip envelope (7/10)
      (fun l : Index B N0 => HarmonicResidual.residualBlock
        (CorrectionInitialization.ActualPrimary.commonContext B) (sourceState B N0)
        (primaryBlock l) (gaussianBlock l).velocity 0) :=
    zeroMean_residual_uniform (CorrectionInitialization.ActualPrimary.commonContext B)
      (operators B) (radius_pos B) (sourceState B N0) (sourceState_mean B N0)
      primaryBlock (fun l => (gaussianBlock l).velocity) 0 hprimary primaryBlock_zeroMode
      primaryBlock_band hphase
      (fun l n => (CorrectionInitialization.ActualPrimary.chartCoefficients_frequency_pos l.2 l.1
        n).ne')
      hdiv (fun l n x _ => envelope_nonneg l n x) (fun l n x _ => envelope_le_one l n x)
      (fun _ _ _ _ _ => rfl) hlinear (by norm_num [ChartScales.kappa])
  have he : (initialState B N0).mean =
      MeanIncrementBounds.updated (sourceState B N0).mean (initialState B N0).mean := by
    rw [sourceState_mean]
    simp only [MeanIncrementBounds.updated, zero_add]
  have hs : MeanIncrementBounds.SmoothTriple strip.domain (sourceState B N0).mean := by
    rw [sourceState_mean]
    exact ⟨fun _ => contDiffOn_const, fun _ => contDiffOn_const, fun _ => contDiffOn_const⟩
  exact CorrectionStep.meanStage_residual_uniform
    (CorrectionInitialization.ActualPrimary.commonContext B) (operators B)
    (by norm_num [ChartScales.kappa]) (radius_pos B) (sourceState B N0) (initialState B N0)
    (initialState B N0).mean he (base_bounds B).smooth hs
    (CorrectionStep.meanIncrement_of_cumulative hmean.velocity) primaryBlock hprimary
    hNormal hFreq hAng hz (fun l => (gaussianBlock l).velocity) 0 0
    (fun _ _ _ => by simpa using (HarmonicResidual.band_zero 0 (D := Point)))
    hzero (by norm_num)

end NavierStokes.ActualInitialization

namespace NavierStokes.ActualInitialization

open Set Filter Function WeightedClasses CorrectionState
open HarmonicMeanInteraction HarmonicWaveInteraction UniformHarmonicInteraction
open scoped ContDiff Topology

noncomputable def zeroBlock {B N0 : ℕ} (l : Index B N0) : HarmonicBlock Point :=
  { primaryBlock l with velocity := 0, pressure := 0 }

theorem zeroBlock_oscillation {B N0 : ℕ} (l : Index B N0) :
    (zeroBlock l).oscillation = 0 := by
  funext n x i
  simp [zeroBlock, HarmonicBlock.oscillation, HarmonicFields.field, HarmonicFields.evaluate,
    HarmonicFields.Coefficients.sum]

/-- Extract the actual linear-good coefficient from the proved primary
field identity, retaining its literal Gaussian coefficient. -/
theorem linearGood_uniform_of_identity (B N0 : ℕ) {γ : ℝ}
    (hprimary : UniformVelocity strip envelope (1/2) (primaryBlock (B := B) (N0 := N0)))
    (hphase : ∀ (l : Index B N0) n, ContDiffOn ℝ ∞ ((primaryPiece l).coefficients.phase n)
      (HarmonicResidual.liftDomain strip.domain))
    (hamp : ∀ (l : Index B N0) n i,
      ContDiffOn ℝ ∞ (fun x => (primaryPiece l).exactCoefficients.amplitude n x i)
        (HarmonicResidual.liftDomain strip.domain))
    (hpressure : ∀ (l : Index B N0) n,
      ContDiffOn ℝ ∞ ((primaryPiece l).exactCoefficients.pressure n)
        (HarmonicResidual.liftDomain strip.domain))
    (hgood : UniformVelocity strip envelope γ (goodBlock (B := B) (N0 := N0)))
    (hidentity : ∀ (l : Index B N0) n x, x ∈ HarmonicResidual.liftDomain strip.domain → ∀ i,
      (primaryPiece l).linearResidual n x i =
        (primaryPiece l).linearGoodField n x i + (primaryPiece l).excluded n x i) :
    UniformVelocity strip envelope γ
      (fun l : Index B N0 => linearGoodBlock (CorrectionInitialization.ActualPrimary.commonContext
        B)
        (primaryBlock l) (primaryBlock l) (gaussianBlock l).velocity) := by
  have hphi (l : Index B N0) (n : ℕ) : ContDiffOn ℝ ∞ (phase l n) strip.domain :=
    (hphase l n).comp (HarmonicWaveInteraction.inclusion (D := Point)).contDiff.contDiffOn
      (fun _ hx => ⟨hx, trivial⟩)
  have hh := CorrectionStep.linearGoodBlock_cancel_uniform
    (CorrectionInitialization.ActualPrimary.commonContext B) primaryBlock primaryBlock zeroBlock
      goodBlock
    (fun l : Index B N0 => (gaussianBlock l).velocity)
    (fun n => (slowGeometry (CorrectionInitialization.ActualPrimary.commonContext B)
      (operators B) (radius_pos B)).radial_class.smooth n)
    (fun _ => contDiffOn_const) (base_bounds B).smooth
    (fun l n i => waveBounds_smooth (waveBounds_each hprimary l) (primaryBlock_zeroMode l) n i)
    (fun l n j => ((pressure_coefficients_uniform B N0 j).each l).smooth n)
    hphi angularMode_ne_zero
    (fun _ _ _ _ _ => by simp [zeroBlock]) goodBlock_symmetric hgood ?_
  · intro i j hj
    simpa only [zeroBlock, Pi.zero_apply, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
      zero_add] using hh i j hj
  · intro l n x hx theta i
    change CorrectionStep.linearBlockField _ (primaryBlock l) (primaryBlock l) n (x,theta) i +
      (zeroBlock l).oscillation n (x,theta) i =
        (goodBlock l).oscillation n (x,theta) i + (gaussianBlock l).oscillation n (x,theta) i
    rw [zeroBlock_oscillation, Pi.zero_apply, Pi.zero_apply, Pi.zero_apply, add_zero,
      goodBlock_represents, gaussianBlock_represents,
      linearBlockField_eq_piece l n (hphase l n) (hamp l n) (hpressure l n) ⟨hx,trivial⟩ i]
    exact hidentity l n (x,theta) ⟨hx,trivial⟩ i

end NavierStokes.ActualInitialization

namespace NavierStokes.ActualInitialization

open Set Function Filter WeightedClasses CorrectionState CorrectionInitialization
open scoped ContDiff Topology

/-- The signed request uses the same active annulus and reserved mean patch. -/
noncomputable def patch : SignedStressPrimitive.Patch where
  a := PrimaryTargetBounds.leftRadius ActualPrimary.nominal
  b := PrimaryTargetBounds.rightRadius ActualPrimary.nominal
  left := ActualPrimary.rankInner
  right := ActualPrimary.rankOuter
  a_pos := PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal
  a_lt_left := ActualPrimary.active_left_before_rank
  left_lt_right := ActualPrimary.rank_radii_ordered
  right_lt_b := ActualPrimary.rank_before_active_right

/-- All stages use one moving strip, common index, and pressure gauge. -/
noncomputable def geometry : SignedMeanGain.Geometry where
  coord := 2 * ActualPrimary.h
  region := ActualPrimary.standardRegion
  patch := patch
  leftWeight := FinalSlowBase.edgeExponent ActualPrimary.nominal / 4
  rightWeight := 1
  left_pos := div_pos (FinalSlowBase.edgeExponent_pos ActualPrimary.nominal) (by norm_num)
  right_pos := zero_lt_one
  epsilon := ChartScales.epsilon ActualPrimary.h
  slow := BaseContextAssembly.slowScale
  epsilon_pos := ChartScales.epsilon_pos ActualPrimary.h
  epsilon_le_one := ChartScales.epsilon_le_one ActualPrimary.h ActualPrimary.outgoing.data.h_pos.le
  slow_ge_one := BaseContextAssembly.one_le_slowScale
  gauge := ActualPrimary.commonGauge
  inner_eq := rfl
  outer_eq := rfl
  exponent_pos := ChartScales.radialExponent_pos ActualPrimary.h
    ActualPrimary.outgoing.data.h_pos.le
  length_eq := fun _ => rfl
  fast := CommonBaseContext.fastCoefficient ActualPrimary.h (CommonWindow.index ActualPrimary.h)
  axial := (0, 1)
  time := (1, 0)
  temporal := TorusInverse.vector .temporal

theorem geometry_strip : geometry.strip = strip := rfl
theorem geometry_slowStrip : geometry.slowStrip = slowStrip := rfl
theorem geometry_operators (B : ℕ) : geometry.operators = (ActualPrimary.commonContext B).operators
  := rfl

theorem initial_primitive (B N0 : ℕ) :
    MeanStateRegularity.PrimitiveData geometry.region geometry.patch.a geometry.patch.b
      (ActualPrimary.commonContext B) (initialState B N0) :=
  ActualInitialCoherence.initialized_primitive B N0

theorem initial_on_overlap (B N0 n m k : ℕ)
    (hi : CommonWindow.index ActualPrimary.h n + k = CommonWindow.index ActualPrimary.h m) :
    PhysicalResidualNaturality.StateOn
      (PhysicalMeanDomain.slowDomain (ActualInitialCoherence.overlap n m))
      (GaugeStateCoherence.bandChartEquiv ActualPrimary.h n m k)
      (GaugeStateCoherence.bandVelocityScale ActualPrimary.h n m)
      (GaugeStateCoherence.bandScale n m) (initialState B N0) (initialState B N0) n m :=
  ActualInitialCoherence.initialized_on_overlap B N0 n m k hi

theorem initial_oscillation_smooth (B N0 : ℕ) :
    WaveStateRegularity.AngularSmooth geometry.domain (initialState B N0).oscillation := by
  rw [initialState_oscillation]
  exact ActualInitialCoherence.seed_smooth B N0

theorem initial_oscillation_support (B N0 : ℕ) :
    WaveStateRegularity.WaveSupport geometry.region geometry.patch.a geometry.patch.b
      (initialState B N0).oscillation := by
  rw [initialState_oscillation]
  exact ActualInitialCoherence.seed_support B N0

theorem initial_oscillation_periodic (B N0 : ℕ) :
    CorrectionStep.OscillationPeriodic geometry.region.carrier (initialState B N0).oscillation := by
  rw [initialState_oscillation]
  intro n R s hs theta
  exact ActualInitialCoherence.seed_velocity_periodic B N0 n R s theta

theorem initial_base_angular (B N0 n : ℕ) (x : Point) (hx : x ∈ geometry.domain) (i : Fin 3) :
    Continuous (fun theta : ℝ => (initialState B N0).errors.base n (x, theta) i) := by
  rw [(initialState_error_components B N0).1]
  exact ActualBaseResidual.baseError_angular_continuous ActualPrimary.certificate
    ActualPrimary.modulation ActualPrimary.upper B n (geometry.region.time_pos _ hx) i

theorem phase_smooth_full {B N0 : ℕ} (l : Index B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((primaryPiece l).coefficients.phase n) (HarmonicResidual.liftDomain
      strip.domain) :=
  (ActualPrimaryCoherence.piece_phase_smooth ActualPrimary.standardRegion l.2 l.1 n).mono
    (fun _ hx => hx.1)

theorem phase_smooth {B N0 : ℕ} (l : Index B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ (phase l n) strip.domain :=
  (phase_smooth_full l n).comp (HarmonicWaveInteraction.inclusion (D := Point)).contDiff.contDiffOn
    (fun _ hx => ⟨hx, trivial⟩)

theorem exact_amplitude_smooth_full {B N0 : ℕ} (l : Index B N0) (n : ℕ) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun x => (primaryPiece l).exactCoefficients.amplitude n x i)
      (HarmonicResidual.liftDomain strip.domain) := by
  have hm : MapsTo (ActualPrimaryCoherence.absoluteChart n)
      (HarmonicResidual.liftDomain strip.domain) ActualPrimaryCoherence.positiveRadialAbsolute := by
    intro x hx
    exact ⟨mul_pos (Real.sqrt_pos.mpr (ChartScales.Q_pos n))
        (BaseContextAssembly.nativeStrip_radius ActualPrimary.nominal ActualPrimary.standardRegion
          hx.1),
      mul_pos (ChartScales.Q_pos n) (strip_time x.1 hx.1)⟩
  have he : (primaryPiece l).exactCoefficients.amplitude n =
      fun x => ChartScales.Q n ^ CoordinateAlgebra.A ActualPrimary.h •
        ActualPrimaryCoherence.absoluteExactAmplitude l.2 l.1 (ActualPrimaryCoherence.absoluteChart
          n x) :=
    funext (ActualPrimaryCoherence.exactAmplitude_representation ActualPrimary.standardRegion l.2
      l.1 n)
  rw [he]
  exact contDiffOn_pi.mp (((ActualPrimaryCoherence.absoluteExactAmplitude_smooth l.2 l.1).comp
    (ActualPrimaryCoherence.absoluteChart n).contDiff.contDiffOn hm).const_smul _) i

theorem exact_pressure_smooth_full {B N0 : ℕ} (l : Index B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((primaryPiece l).exactCoefficients.pressure n)
      (HarmonicResidual.liftDomain strip.domain) :=
  ((ActualPrimaryBounds.chart_cut_pressure_uniform.each (l.2,l.1)).smooth n).mono
    (fun _ hx => hx.1)

theorem initial_meanGood (B N0 n : ℕ) {x : Point} (hT : 0 < x.2.1.1) (i : Fin 3) :
    (initialState B N0).meanGoodResidual (ActualPrimary.commonContext B) n x i =
      (initialState B N0).reducedMeanResidual (ActualPrimary.commonContext B) n x i -
        initialAlias B N0 n x i :=
  ActualInitialMean.initialized_meanGood B N0 n hT i

theorem initialAlias_radial (B N0 n : ℕ) (x : Point) :
    initialAlias B N0 n x 0 = VariableGaugeMean.pressureAliasState ActualPrimary.commonGauge
      (ActualPrimary.commonContext B) (initialState B N0) n (x, 0) 0 := by
  simp only [initialAlias, VariableGaugeMean.temporalAliasState, Matrix.cons_val_zero, zero_add]
  rfl

/-- The remaining radial mean is controlled by the actual measured pressure debt. -/
theorem initial_radial_mean_class (B N0 : ℕ) {alpha : ℝ}
    (hdebt : UnweightedClass slowStrip alpha
      (pressureDefect (ActualPrimary.commonContext B) (initialState B N0))) :
    MeanClass strip alpha (fun n x =>
      (initialState B N0).meanGoodResidual (ActualPrimary.commonContext B) n x 0) := by
  have hr : GaugeRadialResidualBounds.RadialMatch geometry.region.carrier geometry.gauge
      (ActualPrimary.commonContext B).operators := by
    rw [← geometry_operators B]
    exact GaugeRadialResidualBounds.RadialMatch.nativeOperators geometry.region.carrier
      geometry.gauge geometry.epsilon geometry.fast geometry.axial geometry.time geometry.temporal
  have hclass := GaugeRadialResidualBounds.radialMinusAlias_class geometry.region geometry.gauge
    geometry.inner_pos geometry.exponent_pos geometry.left_pos geometry.right_pos
    geometry.epsilon geometry.slow geometry.epsilon_pos geometry.epsilon_le_one geometry.slow_ge_one
    geometry.length_eq (ActualPrimary.commonContext B) (initialState B N0)
    (initial_primitive B N0) hr rfl hdebt
  apply MeanIncrementBounds.class_congr hclass
  intro n x hx
  change (initialState B N0).meanGoodResidual (ActualPrimary.commonContext B) n x 0 = _
  rw [initial_meanGood B N0 n (strip_time x hx) 0, initialAlias_radial]
  rfl

end NavierStokes.ActualInitialization

namespace NavierStokes.ActualInitialization

open Set Function Filter WeightedClasses CorrectionState CorrectionInitialization
open HarmonicResidual HarmonicWaveInteraction
open scoped ContDiff Topology BigOperators

theorem smooth_conjugatePair {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {U : Set D} {f : D → ℂ} (hf : ContDiffOn ℝ ∞ f U) (j : ℤ) :
    SmoothCoefficients U (ErrorHarmonics.conjugatePair j f) := by
  have hs := smoothCoefficients_single (hf.div_const 2) j
  exact hs.add hs.conjugateReverse

theorem primary_coefficients_smooth {B N0 : ℕ} (l : Index B N0) (n : ℕ) (i : Fin 3) :
    SmoothCoefficients strip.domain ((primaryBlock l).velocity n i) := by
  apply smooth_conjugatePair
  exact (exact_amplitude_smooth_full l n i).comp
    (HarmonicWaveInteraction.inclusion (D := Point)).contDiff.contDiffOn (fun _ hx => ⟨hx, trivial⟩)

theorem primary_pressure_smooth {B N0 : ℕ} (l : Index B N0) (n : ℕ) :
    SmoothCoefficients strip.domain ((primaryBlock l).pressure n) := by
  apply smooth_conjugatePair
  exact (exact_pressure_smooth_full l n).comp
    (HarmonicWaveInteraction.inclusion (D := Point)).contDiff.contDiffOn (fun _ hx => ⟨hx, trivial⟩)

theorem gaussian_coefficients_smooth {B N0 : ℕ} (l : Index B N0) (n : ℕ) (i : Fin 3) :
    SmoothCoefficients strip.domain ((gaussianBlock l).velocity n i) := by
  have hm : MapsTo (ActualPrimaryCoherence.absoluteChart n)
      (HarmonicResidual.liftDomain strip.domain) ActualPrimaryCoherence.positiveAbsolute := by
    intro x hx
    exact mul_pos (ChartScales.Q_pos n) (strip_time x.1 hx.1)
  have he : LinearWaveBounds.excludedSlotError (primaryPiece l).directions (primaryPiece l).cutoff
      (primaryPiece l).coefficients.amplitude 0 n =
      fun x => ChartScales.Q n ^ (2 * CoordinateAlgebra.A ActualPrimary.h + 1/2) •
        ActualPrimaryCoherence.absoluteGaussianCoefficient l.2 l.1
          (ActualPrimaryCoherence.absoluteChart n x) :=
    funext (ActualPrimaryCoherence.gaussianCoefficient_representation ActualPrimary.standardRegion
      l.2 l.1 n)
  have hs : ContDiffOn ℝ ∞ (LinearWaveBounds.excludedSlotError (primaryPiece l).directions
      (primaryPiece l).cutoff (primaryPiece l).coefficients.amplitude 0 n)
      (HarmonicResidual.liftDomain strip.domain) := by
    rw [he]
    exact ((ActualPrimaryCoherence.absoluteGaussianCoefficient_smooth l.2 l.1).comp
      (ActualPrimaryCoherence.absoluteChart n).contDiff.contDiffOn hm).const_smul _
  apply smooth_conjugatePair
  exact (contDiffOn_pi.mp hs i).comp
    (HarmonicWaveInteraction.inclusion (D := Point)).contDiff.contDiffOn (fun _ hx => ⟨hx, trivial⟩)

/-- Harmonic solenoidality is extracted from the actual corrected curl. -/
theorem primary_modeSolenoidal {B N0 : ℕ} (l : Index B N0) :
    ModeSolenoidal strip (ActualPrimary.commonContext B) (primaryBlock l) := by
  apply modeSolenoidal_of_full (ActualPrimary.commonContext B) (primaryBlock l)
    (phase_smooth l) (angularMode_ne_zero l) (primary_coefficients_smooth l)
  intro n x hx
  rw [(primaryBlock_represents l).1]
  have hd := ActualPrimaryCoherence.piece_full_divergence ActualPrimary.standardRegion l.2 l.1 n
    (ActualPrimaryCoherence.piece_domain_positive ActualPrimary.standardRegion hx)
  have hax : (PrimaryResidualClass.directions (ActualPrimary.commonContext B)).axialField
      (ActualPrimary.piece ActualPrimary.standardRegion l.2 l.1).strip n =
      liftDirection (contextFrame (ActualPrimary.commonContext B) n).axial :=
    PrimaryResidualClass.directions_axial strip (ActualPrimary.commonContext B) rfl n
  rw [PrimaryResidualClass.directions_radial, hax] at hd
  exact hd

theorem primary_pressure_zero {B N0 : ℕ} (l : Index B N0) (n : ℕ) :
    (primaryBlock l).pressure n 0 = 0 :=
  (SignedWaveUpdate.coefficientBlock_zero_coefficient
    (primaryPiece l).coefficients.frequency (phase l) (angularMode l)
    (fun n x => (primaryPiece l).exactCoefficients.amplitude n (x,0))
    (fun n x => (primaryPiece l).exactCoefficients.pressure n (x,0))).2 n

theorem primary_tangent_carrier {B N0 : ℕ} (l : Index B N0) :
    CorrectionStep.SameCarrier (primaryBlock l) (tangentBlock l) := ⟨rfl, rfl, rfl⟩

/-- All assumptions of local harmonic extraction follow from the actual
initial state and the proved support separation of its primary pieces. -/
theorem initial_extraction_regular (B N0 n : ℕ) :
    LocalResidualGrouping.ExtractionRegular strip.domain (ActualPrimary.commonContext B)
      (initialState B N0) (coefficients B N0).labels (coefficients B N0).blocks
      (coefficients B N0).gaussian (coefficients B N0).aliasCoefficients n := by
  constructor
  · exact contextFrame_regular (ActualPrimary.commonContext B) n contDiffOn_fst
      (fun x hx => (radius_pos B x hx).ne') ((operators B).radialProfile.smooth n)
  · intro i
    fin_cases i
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn ((base_bounds B).radial.smooth n)
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn ((base_bounds B).angular.smooth n)
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn ((base_bounds B).axial.smooth n)
  · intro i
    have hm := (initial_primitive B N0).mean
    fin_cases i
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn ((hm.radial.smooth n).mono
      geometry.strip_subset)
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn ((hm.angular.smooth n).mono
      geometry.strip_subset)
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn ((hm.axial.smooth n).mono
      geometry.strip_subset)
  · exact (((initial_primitive B N0).pressure geometry.inner_pos geometry.exponent_pos
      geometry.length_eq rfl).smooth n).mono geometry.strip_subset
  · intro l hl
    exact ⟨phase_smooth l n, fun i => (primary_coefficients_smooth l n i).realCoefficients,
      (primary_pressure_smooth l n).realCoefficients⟩
  · intro l hl i
    exact gaussian_coefficients_smooth l n i
  · intro l hl i
    exact smoothCoefficients_zero strip.domain
  · intro l hl m hm hlm
    change Disjoint (liftDomain strip.domain ∩ tsupport ((primaryBlock l).oscillation n))
      (liftDomain strip.domain ∩ tsupport ((primaryBlock m).oscillation n))
    rw [(primaryBlock_represents l).1, (primaryBlock_represents m).1,
      LocalResidualGrouping.liftDomain_eq_preimage]
    exact ActualPrimaryCovariance.velocity_tsupport_disjoint n hlm
  · intro l hl
    exact angularMode_ne_zero l n

theorem initial_goodWave_grouped (B N0 n : ℕ) {x : Point × ℝ}
    (hx : x.1 ∈ strip.domain) (i : Fin 3) :
    CorrectionStep.fullGoodWaveResidual (ActualPrimary.commonContext B) (initialState B N0) n x i =
      ∑ l ∈ (coefficients B N0).labels n, (initialResidualBlock l).oscillation n x i :=
  (initialCycleState_represents B N0).fullGoodWaveResidual_grouped_local strip.isOpen_domain
    (initial_extraction_regular B N0 n) ⟨hx, trivial⟩ i

end NavierStokes.ActualInitialization

namespace NavierStokes.ActualInitialization

open Set Function Filter WeightedClasses CorrectionState CorrectionInitialization
open HarmonicCalculus HarmonicWaveInteraction HarmonicMeanInteraction
open scoped ContDiff Topology

/-- Restriction to zero angle and a union of actual copy cells preserve
the constants chosen before labels and copies. -/
theorem local_slice_union {D E I J K : Type}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : StripData D} {C : ℕ → J × K → Set (D × ℝ)} {alpha : ℝ}
    {f : J → ℕ → D × ℝ → E} (e : I → J)
    (hs : ∀ l n, ContDiffOn ℝ ∞ (f l n) (productStrip s).domain)
    (hf : LocalizedWaveBounds.LocalUnweighted (D := D × ℝ) (E := E) (I := J × K) (productStrip s) C
      alpha
      (fun (n : ℕ) (i : J × K) (x : D × ℝ) => f i.1 n x)) :
    LocalizedWaveBounds.LocalUnweighted (D := D) (E := E) (I := I) s
      (fun n i => {x | ∃ k, (x, 0) ∈ C n (e i, k)}) alpha
      (fun n i x => f (e i) n (x, 0)) := by
  refine ⟨fun _ _ _ _ => zero_le_one, ?_, ?_⟩
  · intro n i x hx hc
    exact (((hs (e i) n).comp (inclusion (D := D)).contDiff.contDiffOn
      (fun _ h => h)).contDiffAt (s.isOpen_domain.mem_nhds hx))
  · intro m
    obtain ⟨A, hA, p, hb⟩ := hf.bounds m
    refine ⟨A, hA, p, ?_⟩
    rintro n i x hx ⟨k, hk⟩ j hj
    have hh := norm_jet_comp_linear (productStrip s).isOpen_domain (hs (e i) n)
      (inclusion (D := D)) hx j
    have hp : ‖inclusion (D := D)‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) inclusion_norm
    exact (hh.trans (mul_le_of_le_one_right (norm_nonneg _) hp)).trans
      (hb n (e i, k) (x, 0) hx hk j hj)

noncomputable def fullNormal {B N0 : ℕ} (l : Index B N0) (n : ℕ) :
    Point × ℝ → ProblemStatement.Space :=
  (primaryPiece l).coefficients.normal (primaryPiece l).strip (primaryPiece l).directions n

theorem fullNormal_smooth {B N0 : ℕ} (l : Index B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ (fullNormal l n) (productStrip strip).domain := by
  have hh := CurlClassBounds.phaseNormal_contDiffOn
    (ActualPrimaryCoherence.piece_geometry ActualPrimary.standardRegion B n)
    (ActualPrimaryCoherence.chart_phase_smooth l.2 l.1 n)
  exact hh.mono (ActualPrimaryCoherence.piece_domain_positive ActualPrimary.standardRegion)

theorem phase_slice_derivative {B N0 : ℕ} (l : Index B N0) (n : ℕ)
    {x : Point} (hx : x ∈ strip.domain) (v : Point) :
    fderiv ℝ (phase l n) x v = fderiv ℝ ((primaryPiece l).coefficients.phase n) (x, 0) (v, 0) := by
  have hd := ((phase_smooth_full l n).contDiffAt
    ((HarmonicResidual.liftDomain_open strip.isOpen_domain).mem_nhds
      (show (x, 0) ∈ HarmonicResidual.liftDomain strip.domain from ⟨hx,
        trivial⟩))).differentiableAt (by simp)
  have he := (hd.hasFDerivAt.comp x (inclusion (D := Point)).hasFDerivAt).fderiv
  exact congrArg (fun L : Point →L[ℝ] ℝ => L v) he

theorem slowNormal_component {B N0 : ℕ} (l : Index B N0) (n : ℕ)
    {x : Point} (hx : x ∈ strip.domain) (i : Fin 3) :
    slowNormal (ActualPrimary.commonContext B) (operators B) (radius_pos B) (phase l) n x i =
      if i = 1 then 0 else fullNormal l n (x, 0) i := by
  have hr := PrimaryResidualClass.directions_radial (ActualPrimary.commonContext B) n
  have hz := PrimaryResidualClass.directions_axial strip (ActualPrimary.commonContext B) rfl n
  fin_cases i
  · change fderiv ℝ (phase l n) x _ = fderiv ℝ ((primaryPiece l).coefficients.phase n) (x,0) _
    change fderiv ℝ (phase l n) x _ = fderiv ℝ ((primaryPiece l).coefficients.phase n) (x,0)
      ((PrimaryResidualClass.directions (ActualPrimary.commonContext B)).radialField n (x,0))
    rw [hr]
    exact phase_slice_derivative l n hx _
  · simp [slowNormal, slowGeometry, phaseNormal, along]
  · change fderiv ℝ (phase l n) x _ = fderiv ℝ ((primaryPiece l).coefficients.phase n) (x,0) _
    change fderiv ℝ (phase l n) x _ = fderiv ℝ ((primaryPiece l).coefficients.phase n) (x,0)
      ((PrimaryResidualClass.directions (ActualPrimary.commonContext B)).axialField (productStrip
        strip) n (x,0))
    rw [hz]
    exact phase_slice_derivative l n hx _

theorem phase_angular_affine {B N0 : ℕ} (l : Index B N0) (n : ℕ) :
    CopyAngularInvariance.AffinePhase ((0 : Point),1)
      ((angularMode l n : ℝ) / (primaryPiece l).coefficients.frequency n)
      ((primaryPiece l).coefficients.phase n) := by
  intro x t
  change (ActualPrimary.absolutePhase l.2 l.1 (ActualPrimary.toAbsolute n (x.1 + t • 0), x.2 + t *
    1) /
      (ChartScales.carrier ActualPrimary.h n : ℝ)) = _
  simp only [smul_zero, add_zero, mul_one]
  simp only [ActualPrimary.absolutePhase, angularMode]
  dsimp only [primaryPiece, ActualPrimary.piece, ActualPrimary.chartCoefficients]
  change (_ * (x.2 + t) + _) / _ = (_ * x.2 + _) / _ + (_ / _) * t
  ring

theorem angularMode_from_normal {B N0 : ℕ} (l : Index B N0) (n : ℕ)
    {x : Point} (hx : x ∈ strip.domain) :
    (angularMode l n : ℝ) = (primaryPiece l).coefficients.frequency n * x.1 * fullNormal l n (x, 0)
      1 := by
  have hd := (phase_angular_affine l n).directional_eq
    (((phase_smooth_full l n).contDiffAt
      ((HarmonicResidual.liftDomain_open strip.isOpen_domain).mem_nhds
        (show (x, 0) ∈ HarmonicResidual.liftDomain strip.domain from ⟨hx,
          trivial⟩))).differentiableAt (by simp))
  have hn : fullNormal l n (x,0) 1 =
      ((angularMode l n : ℝ) / (primaryPiece l).coefficients.frequency n) / x.1 := by
    have hc := congrArg (fun a : ℝ => a / x.1) hd
    simp only [fullNormal, LinearWaveBounds.WaveCoefficients.normal, phaseNormal, along,
      Matrix.cons_val_one, Matrix.cons_val_zero, ActualPrimary.piece,
      PrimaryResidualClass.directions, primaryPiece] at hc ⊢
    exact hc
  rw [hn]
  have hK := (ActualPrimary.chartCoefficients_frequency_pos l.2 l.1 n).ne'
  have hR := (BaseContextAssembly.nativeStrip_radius ActualPrimary.nominal
    ActualPrimary.standardRegion hx).ne'
  have hK' : (primaryPiece l).coefficients.frequency n ≠ 0 := hK
  field_simp [hK', hR]

end NavierStokes.ActualInitialization

namespace NavierStokes.ActualInitialization

open Set Function Filter WeightedClasses CorrectionState CorrectionInitialization
open HarmonicWaveInteraction HarmonicMeanInteraction UniformHarmonicInteraction
open scoped ContDiff Topology

noncomputable def meanControlCell {B N0 : ℕ} (n : ℕ) (l : Index B N0) : Set Point :=
  {x | ∃ k : TorusInverse.Frequency, (x,0) ∈ ActualPrimaryBounds.controlCell n ((l.2,l.1), k)}

theorem fullNormal_slice_local (B N0 : ℕ) (i : Fin 3) :
    LocalizedWaveBounds.LocalUnweighted strip meanControlCell 0
      (fun n (l : Index B N0) x => fullNormal l n (x,0) i) := by
  have hs (l : ActualPrimaryBounds.SignedLabel B N0) (n : ℕ) :
      ContDiffOn ℝ ∞ (fun x => ActualPrimaryBounds.chartNormal l n x i) (productStrip strip).domain
        := by
    exact (contDiffOn_piLp 2).mp (fullNormal_smooth (l.2,l.1) n) i
  exact local_slice_union (s := strip) (C := ActualPrimaryBounds.controlCell)
    (f := fun l n x => ActualPrimaryBounds.chartNormal l n x i) Prod.swap hs
    (ActualPrimaryBounds.chart_normal_local.map (EuclideanSpace.proj i))

theorem slowNormal_local (B N0 : ℕ) (i : Fin 3) :
    LocalizedWaveBounds.LocalUnweighted strip meanControlCell 0
      (fun n (l : Index B N0) x => slowNormal (ActualPrimary.commonContext B)
        (operators B) (radius_pos B) (phase l) n x i) := by
  by_cases hi : i = 1
  · subst i
    apply (LocalizedWaveBounds.local_const (s := strip) (K := meanControlCell) (0 : ℝ)).congr_germ
    intro n l x hx hc
    filter_upwards [strip.isOpen_domain.mem_nhds hx] with y hy
    rw [slowNormal_component l n hy]
    simp
  · apply (fullNormal_slice_local B N0 i).congr_germ
    intro n l x hx hc
    filter_upwards [strip.isOpen_domain.mem_nhds hx] with y hy
    rw [slowNormal_component l n hy, ite_eq_right hi]

theorem frequency_local (B N0 : ℕ) :
    LocalizedWaveBounds.LocalUnweighted strip meanControlCell (-(1/2 : ℝ))
      (fun n (l : Index B N0) (_ : Point) => (primaryBlock l).frequency n) :=
  LocalizedWaveBounds.LocalClass.band_const ActualPrimaryBounds.carrier_band

theorem angularFrequency_local (B N0 : ℕ) :
    LocalizedWaveBounds.LocalUnweighted strip meanControlCell (-(1/2 : ℝ))
      (fun n (l : Index B N0) (_ : Point) => ((primaryBlock l).angularFrequency n : ℝ)) := by
  have hrFull : UnweightedClass (productStrip strip) 0 (fun _ (x : Point × ℝ) => x.1.1) :=
    ActualPrimaryBounds.radius_unweighted
  have hr : UnweightedClass strip 0 (fun _ (x : Point) => x.1) :=
    HarmonicWaveInteraction.class_slice (s := strip) (w := fun _ _ => 1) hrFull
  have hm := LocalizedWaveBounds.unweighted_mul
    (LocalizedWaveBounds.unweighted_mul (frequency_local B N0)
      (LocalizedWaveBounds.LocalClass.of_global (K := meanControlCell) hr)) (fullNormal_slice_local
        B N0 1)
  have hm' : LocalizedWaveBounds.LocalUnweighted strip meanControlCell (-(1/2 : ℝ))
      (fun n (l : Index B N0) x => (primaryBlock l).frequency n * x.1 * fullNormal l n (x,0) 1) :=
        by
    simpa only [add_zero] using hm
  apply hm'.congr_germ
  intro n l x hx hc
  filter_upwards [strip.isOpen_domain.mem_nhds hx] with y hy
  exact (angularMode_from_normal l n hy).symm

theorem primary_zero_germ_outside_control {B N0 : ℕ} (n : ℕ) (l : Index B N0)
    {x : Point} (hx : x ∈ strip.domain) (hc : x ∉ meanControlCell n l) (i : Fin 3) (j : ℤ) :
    (primaryBlock l).velocity n i j =ᶠ[𝓝 x] fun _ => 0 := by
  have hzero : (primaryPiece l).exactCoefficients.amplitude n =ᶠ[𝓝 (x,0)] fun _ => 0 := by
    rcases ActualPrimaryBounds.actual_input_cover (l.2,l.1) n (x := (x,0)) hx with ⟨k,hk⟩ | ⟨ha,hp⟩
    · exact (hc ⟨k,hk⟩).elim
    · exact ((ActualPrimaryBounds.actualFamily (B := B) (N0 := N0)).outputs_zero_germs
        ActualPrimaryBounds.fullStrip (ActualPrimaryBounds.directions B) (i := ((l.2,l.1),0)) ha
          hp).2.1
  have hz := hzero.comp_tendsto (inclusion (D := Point)).continuous.continuousAt
  filter_upwards [hz] with y hy
  change (primaryPiece l).exactCoefficients.amplitude n (y,0) = 0 at hy
  change ErrorHarmonics.conjugatePair 1
    (fun z => (primaryPiece l).exactCoefficients.amplitude n (z,0) i) j y = 0
  simp only [ParticularWaveAssembly.pair_apply, hy, Pi.zero_apply, zero_div]
  split_ifs <;> simp

theorem primary_coefficients_uniform (B N0 : ℕ) (i : Fin 3) (j : ℤ) :
    LabelSumBounds.UniformWaveClass strip envelope (1/2)
      (fun l : Index B N0 => fun n x => (primaryBlock l).velocity n i j x) :=
  ((ActualPrimaryBounds.exact_block_uniform (B := B) (N0 := N0)).1 i j).reindex Prod.swap

theorem primary_uniform (B N0 : ℕ) :
    UniformVelocity strip envelope (1/2) (primaryBlock (B := B) (N0 := N0)) :=
  fun i j _ => primary_coefficients_uniform B N0 i j

theorem difference_coefficients_uniform (B N0 : ℕ) (i : Fin 3) (j : ℤ) :
    LabelSumBounds.UniformWaveClass strip envelope (17/25)
      (fun l : Index B N0 => fun n x => (primaryBlock l).velocity n i j x - (tangentBlock
        l).velocity n i j x) := by
  have hd : LabelSumBounds.UniformWaveClass (productStrip strip)
      (fun l : Index B N0 => fun n x => envelope l n x.1) (1 - ChartScales.kappa)
      (fun l n x => (primaryPiece l).exactCoefficients.amplitude n x -
        ((primaryPiece l).coefficients.withCutoff (primaryPiece l).cutoff).amplitude n x) :=
    (ActualPrimaryBounds.chart_difference_uniform (B := B) (N0 := N0)).reindex Prod.swap
  have hs := (UniformBlockBounds.uniform_slice (s := strip)
    (w := fun l n x => Real.sqrt (strip.zeta x) * envelope l n x) hd).map (ContinuousLinearMap.proj
      i)
  have hp := (UniformBlockBounds.pair_uniform hs 1 j).mono_exponent
    (show (17/25 : ℝ) ≤ 1 - ChartScales.kappa by norm_num [ChartScales.kappa])
  apply hp.congr
  intro l n x hx
  exact UniformBlockBounds.pair_sub_apply 1 j
    (fun y => (primaryPiece l).exactCoefficients.amplitude n (y,0) i)
    (fun y => ((primaryPiece l).coefficients.withCutoff (primaryPiece l).cutoff).amplitude n (y,0)
      i) x

theorem good_coefficients_uniform (B N0 : ℕ) (i : Fin 3) (j : ℤ) :
    LabelSumBounds.UniformWaveClass strip envelope (7/10)
      (fun l : Index B N0 => fun n x => (goodBlock l).velocity n i j x) := by
  have hg : LabelSumBounds.UniformWaveClass (productStrip strip)
      (fun l : Index B N0 => fun n x => envelope l n x.1) (1 - 3 * ChartScales.kappa)
      (fun l => (primaryPiece l).linearGood) :=
    (ActualPrimaryBounds.chart_good_uniform (B := B) (N0 := N0)).reindex Prod.swap
  have hs := (UniformBlockBounds.uniform_slice (s := strip)
    (w := fun l n x => Real.sqrt (strip.zeta x) * envelope l n x) hg).map (ContinuousLinearMap.proj
      i)
  exact (UniformBlockBounds.pair_uniform hs 1 j).mono_exponent
    (show (7/10 : ℝ) ≤ 1 - 3 * ChartScales.kappa by norm_num [ChartScales.kappa])

theorem linearGood_uniform (B N0 : ℕ) :
    UniformVelocity strip envelope (7/10)
      (fun l : Index B N0 => linearGoodBlock (ActualPrimary.commonContext B)
        (primaryBlock l) (primaryBlock l) (gaussianBlock l).velocity) := by
  apply linearGood_uniform_of_identity B N0 (primary_uniform B N0) phase_smooth_full
    exact_amplitude_smooth_full exact_pressure_smooth_full
    (fun i j _ => good_coefficients_uniform B N0 i j)
  intro l n x hx i
  exact ActualPrimaryDynamics.linearResidual_eq_on_strip l.2 l.1 n hx.1 i

end NavierStokes.ActualInitialization

namespace NavierStokes.ActualInitialization

open Set Function Filter WeightedClasses CorrectionState CorrectionInitialization
open scoped ContDiff Topology

noncomputable def labelCarrier {B N0 : ℕ} (l : Index B N0) (n : ℕ) : Set Point :=
  ActualInitialExcluded.labelCarrier (l.2, l.1) n

theorem labelCarrier_closed {B N0 : ℕ} (l : Index B N0) (n : ℕ) : IsClosed (labelCarrier l n) :=
  ActualInitialExcluded.labelCarrier_closed (l.2, l.1) n

theorem native_source_core {B N0 : ℕ} (l : Index B N0) (x : ActualSignedGeometry.Native)
    (hg : ActualPrimary.gaussian l.1 x ≠ 0) (hr : ActualPrimary.rawVelocity l.2 l.1 x ≠ 0) :
    x ∈ ActualGaussianCoverage.actualSourceCore ActualPrimary.certificate ActualPrimary.modulation
      (ActualPrimary.choice B N0).prepared l.1 := by
  have hm : ActualPrimary.spatialMask l.1 x.1 ≠ 0 := by
    intro hz
    exact hr (by simp [ActualPrimary.rawVelocity, PartitionedCovariance.amplitude, hz])
  have hs := ActualPrimary.spatialMask_native_support l.1 x.1 hm
  have ht := ActualPrimary.rawVelocity_transverse l.2 l.1 x hr
  have hga : |x.2.2 / ((ActualPrimary.phases B N0 0).L l.1) - 1 / 2| < 1 / 3 :=
    lt_of_not_ge (fun h => hg (GaussianTailFlat.profile_zero h))
  have hL := (ActualPrimary.phases B N0 0).L_pos l.1
  have hlo : (1 / 6 : ℝ) ≤ x.2.2 / ((ActualPrimary.phases B N0 0).L l.1) := by
    linarith [(abs_lt.mp hga).1]
  have hhi : x.2.2 / ((ActualPrimary.phases B N0 0).L l.1) ≤ 5 / 6 := by
    linarith [(abs_lt.mp hga).2]
  refine ⟨hs, ⟨ht.1.le, ht.2.le⟩, ?_, ?_⟩
  · change ((ActualPrimary.phases B N0 0).L l.1 / 1) / 6 ≤ x.2.2
    simpa only [div_eq_mul_inv, inv_one, mul_one, one_mul, mul_comm] using (le_div_iff₀ hL).mp hlo
  · change x.2.2 ≤ 5 * ((ActualPrimary.phases B N0 0).L l.1 / 1) / 6
    simpa only [div_eq_mul_inv, inv_one, mul_one, one_mul, mul_comm, mul_assoc, mul_left_comm] using
      (div_le_iff₀ hL).mp hhi

theorem cut_amplitude_source_support {B N0 : ℕ} (l : Index B N0) (n : ℕ) :
    support (((primaryPiece l).coefficients.withCutoff (primaryPiece l).cutoff).amplitude n) ⊆
      Prod.fst ⁻¹' labelCarrier l n := by
  intro x hx
  by_cases hc : ∃ k : TorusInverse.Frequency,
      (ActualPrimaryDynamics.copyPoint l.2 l.1 n k x).2 ∈ (ActualPrimary.clockWindow l.1).core
  · obtain ⟨k, hk⟩ := hc
    have ha := (ActualPrimaryDynamics.amplitude_germ l.2 l.1 n k hk).eq_of_nhds
    have hpsi := (ActualInitialExcluded.chartCutoff_germ (l.2,l.1) n k hk).eq_of_nhds
    have hg : ActualPrimary.gaussian l.1 (ActualPrimaryDynamics.copyPoint l.2 l.1 n k x) ≠ 0 := by
      intro hz
      apply hx
      change ActualPrimary.chartCutoff l.2 l.1 n x • (ActualPrimary.chartCoefficients l.2
        l.1).amplitude n x = 0
      rw [hpsi, hz, zero_smul]
    have hv : ActualPrimary.attachedRawVelocity l.2 l.1 (ActualPrimaryDynamics.copyPoint l.2 l.1 n
      k x) ≠ 0 := by
      intro hz
      apply hx
      change ActualPrimary.chartCutoff l.2 l.1 n x • (ActualPrimary.chartCoefficients l.2
        l.1).amplitude n x = 0
      rw [ha]
      simp only [ActualPrimaryDynamics.copyAmplitude, hz, map_zero, smul_zero]
    have hr : ActualPrimary.rawVelocity l.2 l.1 (ActualPrimaryDynamics.copyPoint l.2 l.1 n k x) ≠ 0
      := by
      intro hz
      exact hv (by simp [ActualPrimary.attachedRawVelocity, WaveEdgeExtension.nativeExtension,
        WaveEdgeExtension.extension, ActualPrimary.outerRawVelocity, hz])
    exact ⟨k, native_source_core l _ hg hr⟩
  · have hz := (ActualPrimaryDynamics.coefficient_zero_germs l.2 l.1 n (not_exists.mp
    hc)).1.eq_of_nhds
    exact (hx (by
      change ActualPrimary.chartCutoff l.2 l.1 n x • (ActualPrimary.chartCoefficients l.2
        l.1).amplitude n x = 0
      rw [hz, smul_zero])).elim

theorem cut_pressure_source_support {B N0 : ℕ} (l : Index B N0) (n : ℕ) :
    support ((primaryPiece l).exactCoefficients.pressure n) ⊆ Prod.fst ⁻¹' labelCarrier l n := by
  intro x hx
  by_cases hc : ∃ k : TorusInverse.Frequency,
      (ActualPrimaryDynamics.copyPoint l.2 l.1 n k x).2 ∈ (ActualPrimary.clockWindow l.1).core
  · obtain ⟨k, hk⟩ := hc
    have hp := (ActualPrimaryDynamics.pressure_germ l.2 l.1 n k hk).eq_of_nhds
    have hpsi := (ActualInitialExcluded.chartCutoff_germ (l.2,l.1) n k hk).eq_of_nhds
    have hg : ActualPrimary.gaussian l.1 (ActualPrimaryDynamics.copyPoint l.2 l.1 n k x) ≠ 0 := by
      intro hz
      apply hx
      change ActualPrimary.chartCutoff l.2 l.1 n x • (ActualPrimary.chartCoefficients l.2
        l.1).pressure n x = 0
      rw [hpsi, hz, zero_smul]
    have hv : ActualPrimary.attachedRawPressure l.2 l.1 (ActualPrimaryDynamics.copyPoint l.2 l.1 n
      k x) ≠ 0 := by
      intro hz
      apply hx
      change ActualPrimary.chartCutoff l.2 l.1 n x • (ActualPrimary.chartCoefficients l.2
        l.1).pressure n x = 0
      rw [hp]
      simp only [ActualPrimaryDynamics.copyPressure, hz, smul_zero]
    have hr : ActualPrimary.rawVelocity l.2 l.1 (ActualPrimaryDynamics.copyPoint l.2 l.1 n k x) ≠ 0
      := by
      intro hz
      have hzp := ActualPrimary.rawPressure_zero_of_velocity_zero l.2 l.1 _ hz
      exact hv (by simp [ActualPrimary.attachedRawPressure, WaveEdgeExtension.nativeExtension,
        WaveEdgeExtension.extension, ActualPrimary.outerRawPressure, hzp])
    exact ⟨k, native_source_core l _ hg hr⟩
  · have hz := (ActualPrimaryDynamics.coefficient_zero_germs l.2 l.1 n (not_exists.mp
    hc)).2.eq_of_nhds
    exact (hx (by
      change ActualPrimary.chartCutoff l.2 l.1 n x • (ActualPrimary.chartCoefficients l.2
        l.1).pressure n x = 0
      rw [hz, smul_zero])).elim

theorem primary_velocity_zero_outside_source {B N0 : ℕ} (l : Index B N0) (n : ℕ)
    {x : Point} (hx : x ∉ labelCarrier l n) (theta : ℝ) :
    (primaryBlock l).oscillation n (x,theta) = 0 := by
  rw [(primaryBlock_represents l).1]
  have hs := (primaryPiece l).velocity_tsupport_subset_tangent n
  have hc := closure_minimal (cut_amplitude_source_support l n)
    ((labelCarrier_closed l n).preimage continuous_fst)
  exact (notMem_tsupport_iff_eventuallyEq.mp (fun ht => hx (hc (hs ht)))).eq_of_nhds

theorem primary_pressure_zero_outside_source {B N0 : ℕ} (l : Index B N0) (n : ℕ)
    {x : Point} (hx : x ∉ labelCarrier l n) (theta : ℝ) :
    (primaryBlock l).oscillatoryPressure n (x,theta) = 0 := by
  rw [(primaryBlock_represents l).2]
  have hp : (primaryPiece l).exactCoefficients.pressure n (x,theta) = 0 := by
    by_contra hn
    exact hx (cut_pressure_source_support l n hn)
  simp only [PrimaryPiece.pressure, HarmonicCalculus.mode, hp, zero_mul, Complex.zero_re]

theorem gaussian_velocity_zero_outside_source {B N0 : ℕ} (l : Index B N0) (n : ℕ)
    {x : Point} (hx : x ∉ labelCarrier l n) (theta : ℝ) :
    (gaussianBlock l).oscillation n (x,theta) = 0 := by
  rw [gaussianBlock_represents]
  have hg := (ActualInitialExcluded.chartGaussian_zero_germ (l.2,l.1) n
    (x := (x,theta)) hx).eq_of_nhds
  funext i
  change ((ActualInitialExcluded.chartGaussian (l.2,l.1) n (x,theta) i) * _).re = _
  simp only [hg, Pi.zero_apply, zero_mul, Complex.zero_re]

theorem initial_inputSupport {B N0 : ℕ} (l : Index B N0) :
    HarmonicSourceSupport.InputSupportOn geometry.domain (labelCarrier l)
      (primaryBlock l) (gaussianBlock l).velocity 0 := by
  apply HarmonicSourceSupport.InputSupportOn.of_fields _ _ _ (angularMode_ne_zero l)
  · intro n x _ hx theta i
    exact congrFun (primary_velocity_zero_outside_source l n hx theta) i
  · intro n x _ hx theta
    exact primary_pressure_zero_outside_source l n hx theta
  · intro n x _ hx theta i
    exact congrFun (gaussian_velocity_zero_outside_source l n hx theta) i
  · intro n x _ hx theta i
    simp [HarmonicResidual.vectorField, HarmonicResidual.field_zero]

theorem gaussian_coefficients_flat (B N0 : ℕ) (beta : ℝ) (i : Fin 3) (j : ℤ) :
    LabelSumBounds.UniformClass strip (fun _ _ x => Real.sqrt (strip.zeta x)) beta
      (fun l : Index B N0 => fun n x => (gaussianBlock l).velocity n i j x) :=
  (ActualInitialExcluded.gaussianCoefficient_all_gains beta i j).reindex Prod.swap

theorem primary_pressure_symmetric {B N0 : ℕ} (l : Index B N0) (n : ℕ) :
    HarmonicFields.ConjugateSymmetric ((primaryBlock l).pressure n) :=
  ErrorHarmonics.conjugatePair_symmetric 1 _

theorem gaussian_coefficients_symmetric {B N0 : ℕ} (l : Index B N0) (n : ℕ) (i : Fin 3) :
    HarmonicFields.ConjugateSymmetric ((gaussianBlock l).velocity n i) :=
  ErrorHarmonics.conjugatePair_symmetric 1 _

theorem absolute_exact_amplitude_smooth {B N0 : ℕ} (l : Index B N0) :
    ContDiffOn ℝ ∞ (ActualPrimaryCoherence.absoluteExactAmplitude l.2 l.1)
      ActualPrimaryCoherence.positiveAbsolute := by
  have hsub : tsupport (ActualPrimaryCoherence.absoluteExactAmplitude l.2 l.1) ⊆
      tsupport (ActualPrimaryCoherence.absoluteCutAmplitude l.2 l.1) := by
    unfold ActualPrimaryCoherence.absoluteExactAmplitude CurlClassBounds.realizedCoefficient
      CurlClassBounds.curlRemainder
    exact (tsupport_add _ _).trans (union_subset subset_rfl
      ((tsupport_smul_subset_right _ _).trans ((tsupport_smul_subset_right _ _).trans
        ((CurlClassBounds.cylindricalCurl_tsupport_subset _ _ _ _ _).trans
          (CurlClassBounds.coefficient_tsupport_subset _ _ _ _ _ _)))))
  intro x hx
  by_cases hr : 0 < x.1.1.1
  · exact ((ActualPrimaryCoherence.absoluteExactAmplitude_smooth l.2 l.1).contDiffAt
      (ActualPrimaryCoherence.positiveRadialAbsolute_open.mem_nhds ⟨hr,hx⟩)).contDiffWithinAt
  · have ha := (ActualPrimaryCoherence.absolutePair_zero_germ_outside l.2 l.1 hx
      (ActualPrimaryCoherence.amplitudeRadius_outside_nonpositive l.1 (le_of_not_gt hr))).1
    have hc : ActualPrimaryCoherence.absoluteCutAmplitude l.2 l.1 =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [ha] with y hy
      simp only [ActualPrimaryCoherence.absoluteCutAmplitude, hy, smul_zero]
    have he : ActualPrimaryCoherence.absoluteExactAmplitude l.2 l.1 =ᶠ[𝓝 x] fun _ => 0 :=
      notMem_tsupport_iff_eventuallyEq.mp
        (fun h => (notMem_tsupport_iff_eventuallyEq.mpr hc) (hsub h))
    exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt

theorem exact_amplitude_positive_smooth {B N0 : ℕ} (l : Index B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((primaryPiece l).exactCoefficients.amplitude n)
      ActualPrimaryCoherence.positiveChart := by
  have hm : MapsTo (ActualPrimaryCoherence.absoluteChart n) ActualPrimaryCoherence.positiveChart
      ActualPrimaryCoherence.positiveAbsolute := by
    intro x hx
    exact mul_pos (ChartScales.Q_pos n) hx
  exact (((absolute_exact_amplitude_smooth l).comp
    (ActualPrimaryCoherence.absoluteChart n).contDiff.contDiffOn hm).const_smul
      (ChartScales.Q n ^ CoordinateAlgebra.A ActualPrimary.h)).congr
    (fun x _ => ActualPrimaryCoherence.exactAmplitude_representation ActualPrimary.standardRegion
      l.2 l.1 n x)

theorem exact_pressure_positive_smooth {B N0 : ℕ} (l : Index B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ ((primaryPiece l).exactCoefficients.pressure n)
      ActualPrimaryCoherence.positiveChart := by
  have hm : MapsTo (ActualPrimaryCoherence.absoluteChart n) ActualPrimaryCoherence.positiveChart
      ActualPrimaryCoherence.positiveAbsolute := by
    intro x hx
    exact mul_pos (ChartScales.Q_pos n) hx
  exact (cutoff_smooth l n).contDiffOn.smul
    (((ActualPrimaryCoherence.absolutePressureCoefficient_smooth l.2 l.1).comp
      (ActualPrimaryCoherence.absoluteChart n).contDiff.contDiffOn hm).const_smul
        (ChartScales.Q n ^ (2 * CoordinateAlgebra.A ActualPrimary.h)))

theorem gaussian_positive_smooth {B N0 : ℕ} (l : Index B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ (ActualInitialExcluded.chartGaussian (l.2,l.1) n)
      ActualPrimaryCoherence.positiveChart := by
  have hm : MapsTo (ActualPrimaryCoherence.absoluteChart n) ActualPrimaryCoherence.positiveChart
      ActualPrimaryCoherence.positiveAbsolute := by
    intro x hx
    exact mul_pos (ChartScales.Q_pos n) hx
  exact (((ActualPrimaryCoherence.absoluteGaussianCoefficient_smooth l.2 l.1).comp
    (ActualPrimaryCoherence.absoluteChart n).contDiff.contDiffOn hm).const_smul
      (ChartScales.Q n ^ (2 * CoordinateAlgebra.A ActualPrimary.h + 1/2))).congr
    (fun x _ => ActualPrimaryCoherence.gaussianCoefficient_representation
      ActualPrimary.standardRegion l.2 l.1 n x)

theorem primary_coefficients_smooth_domain {B N0 : ℕ} (l : Index B N0) (n : ℕ) (i : Fin 3) (j : ℤ) :
    ContDiffOn ℝ ∞ ((primaryBlock l).velocity n i j) geometry.domain := by
  apply smooth_conjugatePair
  exact ((contDiffOn_pi.mp (exact_amplitude_positive_smooth l n) i).comp
    (HarmonicWaveInteraction.inclusion (D := Point)).contDiff.contDiffOn
      (fun x hx => geometry.region.time_pos x.2.1 hx))

theorem pressure_coefficients_smooth_domain {B N0 : ℕ} (l : Index B N0) (n : ℕ) (j : ℤ) :
    ContDiffOn ℝ ∞ ((primaryBlock l).pressure n j) geometry.domain := by
  apply smooth_conjugatePair
  exact (exact_pressure_positive_smooth l n).comp
    (HarmonicWaveInteraction.inclusion (D := Point)).contDiff.contDiffOn
      (fun x hx => geometry.region.time_pos x.2.1 hx)

theorem gaussian_coefficients_smooth_domain {B N0 : ℕ} (l : Index B N0) (n : ℕ) (i : Fin 3) (j : ℤ)
  :
    ContDiffOn ℝ ∞ ((gaussianBlock l).velocity n i j) geometry.domain := by
  apply smooth_conjugatePair
  exact (contDiffOn_pi.mp (gaussian_positive_smooth l n) i).comp
    (HarmonicWaveInteraction.inclusion (D := Point)).contDiff.contDiffOn
      (fun x hx => geometry.region.time_pos x.2.1 hx)

theorem initial_oscillatoryPressure_smooth (B N0 n : ℕ) :
    ContDiffOn ℝ ∞ ((initialState B N0).oscillatoryPressure n) (geometry.domain ×ˢ univ) := by
  have he : (initialState B N0).oscillatoryPressure n =
      fun x => ∑ l ∈ (coefficients B N0).labels n, (primaryPiece l).pressure n x := by
    funext x
    simp [initialState, rankState, temporalState, primaryState, sourceState, bandSeed,
      GaugeInitialization.retainPressureAlias, VariableGaugeMean.rankStageState,
      VariableGaugeMean.temporalStageState, VariableGaugeMean.reconstructState, State.addIncrement]
  rw [he]
  apply ContDiffOn.sum
  intro l hl
  exact (ActualPrimaryCoherence.piece_pressure_smooth ActualPrimary.standardRegion l.2 l.1 n).mono
    (fun x hx => geometry.region.time_pos x.1.2.1 hx.1)

end NavierStokes.ActualInitialization

namespace NavierStokes.ActualInitialization

open Set Function Filter WeightedClasses CorrectionState CorrectionInitialization
open HarmonicWaveInteraction UniformHarmonicInteraction
open scoped ContDiff Topology BigOperators

theorem initial_cumulative (B N0 : ℕ) : CumulativeBounds strip (initialState B N0) :=
  ActualInitialMean.initial_cumulative_bounds B N0

theorem initial_mean (B N0 : ℕ) :
    MeanResidualBounds strip (1/5) (ActualPrimary.commonContext B) (initialState B N0) :=
  ActualInitialMean.initial_mean_bounds B N0

theorem initial_debt (B N0 : ℕ) :
    DefectBounds slowStrip (1/5) (ActualPrimary.commonContext B) (initialState B N0) :=
  ActualInitialMean.initial_debt_bounds B N0

theorem initial_zeroMasses (B N0 : ℕ) :
    GaugeMassPreservation.ZeroMassesOn geometry.region.carrier (initialState B N0) :=
  ActualInitialMean.initial_zeroMasses B N0

theorem initial_covariance (B N0 : ℕ) (i j : Fin 3) :
    MeanClass strip 1 ((initialState B N0).covariance i j) := by
  rw [initialState_covariance]
  exact (ActualInitialMean.covariance_bounds B N0).1 i j

theorem initial_axis_flat (B N0 : ℕ) (beta : ℝ) : MeanClass strip beta (initialAlias B N0) :=
  ActualInitialExcluded.initialAlias_all_gains B N0 beta

theorem initial_meanHypotheses (B N0 : ℕ) :
    LiftedMeanResidual.MeanHypotheses strip.domain (ActualPrimary.commonContext B) (initialState B
      N0) :=
  ActualInitialMeanEquation.initialized_meanHypotheses B N0

theorem initial_residual_uniform (B N0 : ℕ) :
    UniformVelocity strip envelope (7/10) (initialResidualBlock (B := B) (N0 := N0)) :=
  initial_residual_uniform_of_primary B N0 (primary_uniform B N0) (linearGood_uniform B N0)
    phase_smooth primary_modeSolenoidal (slowNormal_local B N0) (frequency_local B N0)
    (angularFrequency_local B N0)
    (fun n l _x hx hc i j _ => primary_zero_germ_outside_control n l hx hc i j)
    (initial_cumulative B N0)

theorem gaussianBlock_zeroMode {B N0 : ℕ} (l : Index B N0) : ZeroMode (gaussianBlock l) := by
  intro n i
  ext x
  change ErrorHarmonics.conjugatePair 1 _ 0 x = 0
  simp only [ParticularWaveAssembly.pair_apply]
  norm_num

theorem initial_gaussian_mean_zero (B N0 : ℕ) :
    CorrectionStep.angularMeanVector (initialState B N0).errors.gaussian = 0 := by
  rw [(initialState_error_components B N0).2.1]
  simpa only [gaussianBlock_represents] using
    CorrectionStep.fieldSum_angularMean_zero (coefficients B N0).labels gaussianBlock
      gaussianBlock_zeroMode angularMode_ne_zero

/-- The literal same-choice initialized state satisfies every analytic,
support, regularity, and representation field used by the correction cycle. -/
theorem initial_invariant (B N0 : ℕ) :
    CorrectionStep.CycleAnalyticInvariant geometry (ActualPrimary.commonContext B)
      (tangentBlock (B := B) (N0 := N0)) envelope labelCarrier (1/5) (initialCycleState B N0) where
  representation := initialCycleState_represents B N0
  bands := coefficients_band B N0
  realCoefficients := ⟨primaryBlock_symmetric, primary_pressure_symmetric,
    gaussian_coefficients_symmetric⟩
  inputSupport := initial_inputSupport
  sourceBand := initialResidualBlock_band
  zeroVelocity := primaryBlock_zeroMode
  zeroPressure := primary_pressure_zero
  carrier := primary_tangent_carrier
  phase := phase_smooth
  frequency := fun l n => (ActualPrimary.chartCoefficients_frequency_pos l.2 l.1 n).ne'
  angular := angularMode_ne_zero
  coefficientSmooth := primary_coefficients_smooth_domain
  pressureCoefficientSmooth := pressure_coefficients_smooth_domain
  gaussianCoefficientSmooth := gaussian_coefficients_smooth_domain
  solenoidal := primary_modeSolenoidal
  wave := primary_coefficients_uniform B N0
  pressure := pressure_coefficients_uniform B N0
  difference := difference_coefficients_uniform B N0
  cumulative := initial_cumulative B N0
  covariance := initial_covariance B N0
  residual := by
    convert! initial_residual_uniform B N0 using 1
    norm_num
  mean := initial_mean B N0
  meanHypotheses := initial_meanHypotheses B N0
  debt := initial_debt B N0
  primitives := initial_primitive B N0
  reconstructed := initialState_reconstructed B N0
  masses := initial_zeroMasses B N0
  oscillationSmooth := initial_oscillation_smooth B N0
  oscillatoryPressureSmooth := initial_oscillatoryPressure_smooth B N0
  oscillationPeriodic := initial_oscillation_periodic B N0
  oscillationSupport := initial_oscillation_support B N0
  gaussianFlat := gaussian_coefficients_flat B N0
  gaussianMean := initial_gaussian_mean_zero B N0
  aliasCoefficients := fun _ => rfl
  axisFlat := initial_axis_flat B N0
  baseAngular := initial_base_angular B N0

/-- The radial component is included: all three actual good mean
residuals have exponent six fifths. -/
theorem initial_mean_all_components (B N0 : ℕ) (i : Fin 3) :
    MeanClass strip (6/5) (fun n x =>
      (initialState B N0).meanGoodResidual (ActualPrimary.commonContext B) n x i) := by
  have he : (1 + (1 : ℝ)/5) = 6/5 := by norm_num
  fin_cases i
  · apply initial_radial_mean_class
    simpa only [debt, Matrix.cons_val_zero, he] using initial_debt B N0 0
  · have hc := (initial_mean B N0).angular
    simp only [he] at hc
    exact hc
  · have hc := (initial_mean B N0).axial
    simp only [he] at hc
    exact hc

theorem initial_fullDivergence (B N0 n : ℕ) {x : Point × ℝ} (hx : x.1 ∈ strip.domain) :
    CorrectionStep.fullDivergence (ActualPrimary.commonContext B) (initialState B N0) n x = 0 :=
  ActualInitialMeanEquation.initialized_fullDivergence B N0 n ⟨hx,trivial⟩

/-- Exact decomposition of the actual differentiated PDE, with both the
mean and every stored excluded error retained. -/
theorem initial_fullResidual (B N0 n : ℕ) {x : Point × ℝ} (hx : x.1 ∈ strip.domain) (i : Fin 3) :
    CorrectionStep.fullResidual (ActualPrimary.commonContext B) (initialState B N0) n x i =
      (∑ l ∈ (coefficients B N0).labels n, (initialResidualBlock l).oscillation n x i) +
      (initialState B N0).meanGoodResidual (ActualPrimary.commonContext B) n x.1 i +
      (initialState B N0).errors.total n x i := by
  have he := congrArg (fun f : Oscillation Point => f n x i)
    (CorrectionStep.fullResidual_decomposition (ActualPrimary.commonContext B) (initialState B N0))
  change CorrectionStep.fullResidual _ _ n x i = CorrectionStep.fullGoodWaveResidual _ _ n x i +
    CorrectionStep.angularMeanVector (CorrectionStep.fullGoodResidual _ _) n x.1 i + _ at he
  rw [initial_goodWave_grouped B N0 n hx i,
    CorrectionStep.angularMean_fullGoodResidual (initial_meanHypotheses B N0) n hx i] at he
  exact he


/-- All derivatives of the complete stored excluded error satisfy estimates for every
power on the full angular and auxiliary lift. -/
theorem initial_excluded_all_gains (B N0 : ℕ) (beta : ℝ) :
    UnweightedClass (HarmonicWaveInteraction.productStrip strip) beta
      (initialState B N0).errors.total :=
  ActualInitialExcluded.initializedErrors_vector_all_gains B N0 beta

theorem initial_excluded_component_all_gains (B N0 : ℕ) (beta : ℝ) (i : Fin 3) :
    UnweightedClass (HarmonicWaveInteraction.productStrip strip) beta
      (fun n x => (initialState B N0).errors.total n x i) :=
  ActualInitialExcluded.initializedErrors_all_gains B N0 beta i

end NavierStokes.ActualInitialization

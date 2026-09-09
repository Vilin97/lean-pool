/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualBaseResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPrimaryBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPrimaryCovariance
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPrimaryCoherence
import LeanPool.NavierStokesAndEuler.NavierStokes.UniformBlockBounds

/-!
# Mean estimates for the chosen initial primary family

This module uses the literal primary choice, band labels, common gauge and
rank data from `CorrectionInitialization.ActualPrimary`.  In particular the
stored base error is the actual base residual, whose angular continuity is
used only on the positive-time domain.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualInitialMean

open Set Filter CorrectionState CorrectionInitialization WeightedClasses
open scoped ContDiff Topology BigOperators


/-- Point: an abbreviation for `LocalSignedRequest.Point`. -/
abbrev Point := LocalSignedRequest.Point
/-- Index: an abbreviation for `ActualPrimary.Label B N0 × Fin 2`. -/
abbrev Index (B N0 : ℕ) := ActualPrimary.Label B N0 × Fin 2

/-- Strip, given by `BaseContextAssembly.nativeStrip ActualPrimary.nominal
ActualPrimary.standardRegion`. -/
noncomputable def strip : StripData Point :=
  BaseContextAssembly.nativeStrip ActualPrimary.nominal ActualPrimary.standardRegion

/-- Slow strip, constructed using `PhysicalMeanDomain.localSlowStripData`. -/
noncomputable def slowStrip : StripData TorusInverse.Plane :=
  PhysicalMeanDomain.localSlowStripData ActualPrimary.standardRegion.carrier
    ActualPrimary.standardRegion.isOpen (ChartScales.epsilon ActualPrimary.h)
    BaseContextAssembly.slowScale (ChartScales.epsilon_pos ActualPrimary.h)
    (ChartScales.epsilon_le_one ActualPrimary.h ActualPrimary.outgoing.data.h_pos.le)
    BaseContextAssembly.one_le_slowScale

/-- Primary piece, given by `ActualPrimary.piece ActualPrimary.standardRegion l.2 l.1`. -/
noncomputable def primaryPiece {B N0 : ℕ} (l : Index B N0) : PrimaryPiece (Point × ℝ) :=
  ActualPrimary.piece ActualPrimary.standardRegion l.2 l.1

/-- Base error, given by `ActualBaseResidual.baseError ActualPrimary.certificate
ActualPrimary.modulation ActualPrimary.upper B`. -/
noncomputable def baseError (B : ℕ) : Oscillation Point :=
  ActualBaseResidual.baseError ActualPrimary.certificate ActualPrimary.modulation
      ActualPrimary.upper B

/-- Seed, given by `bandSeed (ActualPrimary.activeLabels ActualPrimary.standardRegion B N0)
primaryPiece (baseError B)`. -/
noncomputable def seed (B N0 : ℕ) : State Point :=
  bandSeed (ActualPrimary.activeLabels ActualPrimary.standardRegion B N0) primaryPiece (baseError B)

/-- Axial, given by `((0, 1), 0)`. -/
noncomputable def axial : TorusInverse.Plane × TorusInverse.Plane := ((0, 1), 0)

/-- Primary, given by `VariableGaugeMean.reconstructState ActualPrimary.commonGauge
(ActualPrimary.commonContext B) (seed B N0)`. -/
noncomputable def primary (B N0 : ℕ) : State Point :=
  VariableGaugeMean.reconstructState ActualPrimary.commonGauge (ActualPrimary.commonContext B)
      (seed B N0)

/-- Temporal, constructed using `VariableGaugeMean.temporalStageState`. -/
noncomputable def temporal (B N0 : ℕ) : State Point :=
  VariableGaugeMean.temporalStageState ActualPrimary.commonGauge ActualPrimary.h
    (CommonWindow.index ActualPrimary.h) axial (ActualPrimary.commonContext B) (primary B N0)

/-- Ranked, constructed using `VariableGaugeMean.rankStageState`. -/
noncomputable def ranked (B N0 : ℕ) : State Point :=
  VariableGaugeMean.rankStageState ActualPrimary.commonGauge ActualPrimary.rankData axial
    (ActualPrimary.commonContext B) (temporal B N0)

/-- Initialized, constructed using `GaugeInitialization.initializedBands`. -/
noncomputable def initialized (B N0 : ℕ) : State Point :=
  GaugeInitialization.initializedBands ActualPrimary.commonGauge ActualPrimary.rankData
    ActualPrimary.h (CommonWindow.index ActualPrimary.h) axial (ActualPrimary.commonContext B)
    (ActualPrimary.activeLabels ActualPrimary.standardRegion B N0) primaryPiece (baseError B)

/-- Initial alias, constructed using `VariableGaugeMean.temporalAliasState`. -/
noncomputable def initialAlias (B N0 : ℕ) (n : ℕ) (x : Point) : Fin 3 → ℝ :=
  VariableGaugeMean.temporalAliasState ActualPrimary.commonGauge ActualPrimary.h
      (CommonWindow.index ActualPrimary.h) (ActualPrimary.commonContext B) (primary B N0) n (x, 0) +
    VariableGaugeMean.pressureAliasState ActualPrimary.commonGauge (ActualPrimary.commonContext B)
      (ranked B N0) n (x, 0)

section AngularBookkeeping

variable {B N0 : ℕ}

/-- Phase, given by `(primaryPiece l).coefficients.phase n (x, 0)`. -/
noncomputable def phase (l : Index B N0) (n : ℕ) (x : Point) : ℝ :=
  (primaryPiece l).coefficients.phase n (x, 0)

/-- Angular mode, constructed using `PrimaryGeometryAssembly.angularMode`. -/
noncomputable def angularMode (l : Index B N0) (_n : ℕ) : ℤ :=
  PrimaryGeometryAssembly.angularMode ActualPrimary.certificate ActualPrimary.modulation
    (ActualPrimary.choice B N0).prepared l.2 l.1

theorem angularMode_ne_zero (l : Index B N0) (n : ℕ) : angularMode l n ≠ 0 :=
  PrimaryGeometryAssembly.angularMode_ne_zero ActualPrimary.certificate ActualPrimary.modulation
    (ActualPrimary.choice B N0).prepared l.2 l.1

theorem phase_split (l : Index B N0) (n : ℕ) (x : Point) (theta : ℝ) :
    (primaryPiece l).coefficients.frequency n * (primaryPiece l).coefficients.phase n (x, theta) =
      (primaryPiece l).coefficients.frequency n * phase l n x + (angularMode l n : ℝ) * theta := by
  change (ActualPrimary.chartCoefficients l.2 l.1).frequency n *
      (ActualPrimary.chartCoefficients l.2 l.1).phase n (x, theta) =
    (ActualPrimary.chartCoefficients l.2 l.1).frequency n *
      (ActualPrimary.chartCoefficients l.2 l.1).phase n (x, 0) + _
  rw [ActualPrimary.chartCoefficients_phase, ActualPrimary.chartCoefficients_phase]
  simp only [ActualPrimary.absolutePhase, angularMode, mul_zero, zero_add]
  ring

theorem cutoff_smooth (l : Index B N0) (n : ℕ) : ContDiff ℝ ∞ ((primaryPiece l).cutoff n) :=
  (ActualPrimary.periodicGaussian_smooth l.2 l.1).comp
    ((ActualPrimary.toAbsolute_smooth n).snd.comp contDiff_fst)

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

theorem tangent_amplitude_angle (l : Index B N0) :
    ErrorHarmonics.AngleIndependent
      ((primaryPiece l).coefficients.withCutoff (primaryPiece l).cutoff).amplitude := fun _ _ _ =>
          rfl

theorem gaussian_mean_zero (l : Index B N0) :
    CorrectionStep.angularMeanVector (primaryPiece l).excluded = 0 :=
  (primaryPiece l).excluded_mean_zero (phase l) (angularMode l) (angularMode_ne_zero l)
    (cutoff_smooth l) (cutoff_angle l) (amplitude_angle l) (phase_split l)

theorem gaussian_angularContinuous (l : Index B N0) :
    CorrectionStep.AngularContinuous (primaryPiece l).excluded :=
  (primaryPiece l).excluded_angularContinuous (phase l) (angularMode l)
    (cutoff_smooth l) (cutoff_angle l) (amplitude_angle l) (phase_split l)

/-- Only continuity along the single angular integration fiber is needed. -/
theorem meanGoodResidual_at {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (c : Context D) (u : State D) (n : ℕ) (x : D) (i : Fin 3)
    (hb : Continuous (fun theta : ℝ => u.errors.base n (x, theta) i))
    (hg : Continuous (fun theta : ℝ => u.errors.gaussian n (x, theta) i))
    (ha : Continuous (fun theta : ℝ => u.errors.aliasError n (x, theta) i)) :
    u.meanGoodResidual c n x i = u.reducedMeanResidual c n x i -
      HarmonicResidual.realAngularMean (fun theta => u.errors.gaussian n (x, theta) i) -
      HarmonicResidual.realAngularMean (fun theta => u.errors.aliasError n (x, theta) i) := by
  change u.reducedMeanResidual c n x i +
    HarmonicResidual.realAngularMean (fun theta => u.errors.base n (x, theta) i) -
    HarmonicResidual.realAngularMean (fun theta =>
      u.errors.base n (x, theta) i + u.errors.gaussian n (x, theta) i +
      u.errors.aliasError n (x, theta) i) = _
  rw [HarmonicResidual.realAngularMean_add (hb.fun_add hg) ha,
    HarmonicResidual.realAngularMean_add hb hg]
  ring

theorem initialized_meanGood (B N0 n : ℕ) {x : Point} (hT : 0 < x.2.1.1) (i : Fin 3) :
    (initialized B N0).meanGoodResidual (ActualPrimary.commonContext B) n x i =
      (initialized B N0).reducedMeanResidual (ActualPrimary.commonContext B) n x i - initialAlias B
          N0 n x i := by
  obtain ⟨hb, hg, ha⟩ := GaugeInitialization.initializedBands_error_components
    ActualPrimary.commonGauge ActualPrimary.rankData ActualPrimary.h
    (CommonWindow.index ActualPrimary.h) axial (ActualPrimary.commonContext B)
    (ActualPrimary.activeLabels ActualPrimary.standardRegion B N0) primaryPiece (baseError B)
  change (initialized B N0).errors.base = _ at hb
  change (initialized B N0).errors.gaussian = _ at hg
  change (initialized B N0).errors.aliasError = _ at ha
  have hbc : Continuous (fun theta : ℝ => (initialized B N0).errors.base n (x, theta) i) := by
    rw [hb]
    exact ActualBaseResidual.baseError_angular_continuous ActualPrimary.certificate
      ActualPrimary.modulation ActualPrimary.upper B n hT i
  have hgc : Continuous (fun theta : ℝ => (initialized B N0).errors.gaussian n (x, theta) i) := by
    rw [hg]
    exact continuous_finsetSum _ (fun l _ => gaussian_angularContinuous l n x i)
  have hac : Continuous (fun theta : ℝ => (initialized B N0).errors.aliasError n (x, theta) i) := by
    rw [ha]
    change Continuous (fun _ : ℝ => initialAlias B N0 n x i)
    exact continuous_const
  rw [meanGoodResidual_at _ _ n x i hbc hgc hac]
  have hgz : HarmonicResidual.realAngularMean
      (fun theta => (initialized B N0).errors.gaussian n (x, theta) i) = 0 := by
    change CorrectionStep.angularMeanVector (initialized B N0).errors.gaussian n x i = 0
    rw [hg, angularMeanVector_fieldSum _ _
      (fun n l _ x i => gaussian_angularContinuous l n x i)]
    simp only [gaussian_mean_zero, Pi.zero_apply, Finset.sum_const_zero]
  rw [hgz, sub_zero]
  congr 1
  rw [ha]
  change HarmonicResidual.realAngularMean (fun _ : ℝ => initialAlias B N0 n x i) = _
  exact HarmonicResidual.realAngularMean_const _

end AngularBookkeeping

section CovarianceInputs

variable {B N0 : ℕ}

/-- Envelope, given by `ActualPrimaryBounds.fullEnvelope (l.2, l.1) n (x, 0)`. -/
noncomputable def envelope (l : Index B N0) (n : ℕ) (x : Point) : ℝ :=
  ActualPrimaryBounds.fullEnvelope (l.2, l.1) n (x, 0)

theorem envelope_nonneg (l : Index B N0) (n : ℕ) (x : Point) : 0 ≤ envelope l n x :=
  ActualPrimaryBounds.fullEnvelope_nonneg (l.2, l.1) n (x, 0)

theorem envelope_le_one (l : Index B N0) (n : ℕ) (x : Point) : envelope l n x ≤ 1 :=
  ActualPrimaryBounds.fullEnvelope_le_one (l.2, l.1) n (x, 0)

theorem tangent_amplitude_uniform :
    LabelSumBounds.UniformWaveClass strip envelope (1 / 2)
      (fun l : Index B N0 => fun n x =>
        ((primaryPiece l).coefficients.withCutoff (primaryPiece l).cutoff).amplitude n (x, 0)) := by
  have hh := ActualPrimaryBounds.chart_cut_amplitude_uniform (B := B) (N0 := N0)
  change LabelSumBounds.UniformClass (HarmonicWaveInteraction.productStrip strip)
    (fun l n x => Real.sqrt (strip.zeta x.1) * ActualPrimaryBounds.meanEnvelope l n x.1)
    (1 / 2) _ at hh
  have hr : LabelSumBounds.UniformWaveClass strip ActualPrimaryBounds.meanEnvelope (1 / 2)
      (fun l : ActualPrimaryBounds.SignedLabel B N0 => fun n x =>
        ((ActualPrimary.chartCoefficients l.1 l.2).withCutoff
          (ActualPrimary.chartCutoff l.1 l.2)).amplitude n (x, 0)) :=
    UniformBlockBounds.uniform_slice hh
  exact hr.reindex (fun l : Index B N0 => (l.2, l.1))

theorem seed_angularSmooth (B N0 : ℕ) :
    WaveStateRegularity.AngularSmooth
      (PhysicalMeanDomain.slowDomain ActualPrimary.standardRegion.carrier) (seed B N0).oscillation
          := by
  intro n i
  change ContDiffOn ℝ ∞ (fun p =>
      ∑ l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n,
        (primaryPiece l).velocity n p i)
    (HarmonicResidual.liftDomain (PhysicalMeanDomain.slowDomain
        ActualPrimary.standardRegion.carrier))
  apply ContDiffOn.sum
  intro l _
  exact (contDiffOn_pi.mp (ActualPrimaryCoherence.piece_velocity_smooth
    ActualPrimary.standardRegion l.2 l.1 n) i).mono
      (fun p hp => ActualPrimary.standardRegion.time_pos _ hp.1)

theorem seed_covariance_smooth (B N0 : ℕ) (i j : Fin 3) :
    MeanIncrementBounds.SmoothOn (PhysicalMeanDomain.slowDomain
        ActualPrimary.standardRegion.carrier)
      ((seed B N0).covariance i j) :=
  WaveStateRegularity.bilinearCovariance_smooth
    (PhysicalMeanDomain.slowDomain_open ActualPrimary.standardRegion.isOpen)
    (seed_angularSmooth B N0) (seed_angularSmooth B N0) i j

theorem tangent_angularSmooth (B N0 : ℕ) :
    WaveStateRegularity.AngularSmooth
      (PhysicalMeanDomain.slowDomain ActualPrimary.standardRegion.carrier)
      (ActualPrimaryCovariance.tangentSum B N0) := by
  intro n i
  apply ContDiffOn.sum
  intro l _
  exact (contDiffOn_pi.mp (ActualPrimaryCoherence.piece_tangentVelocity_smooth
    ActualPrimary.standardRegion l.2 l.1 n) i).mono
      (fun p hp => ActualPrimary.standardRegion.time_pos _ hp.1)

theorem tangent_covariance_smooth (B N0 : ℕ) (i j : Fin 3) :
    MeanIncrementBounds.SmoothOn (PhysicalMeanDomain.slowDomain
        ActualPrimary.standardRegion.carrier)
      (ActualPrimaryCovariance.tangentCovariance B N0 i j) :=
  WaveStateRegularity.bilinearCovariance_smooth
    (PhysicalMeanDomain.slowDomain_open ActualPrimary.standardRegion.isOpen)
    (tangent_angularSmooth B N0) (tangent_angularSmooth B N0) i j

theorem seed_waveSupport (B N0 : ℕ) :
    WaveStateRegularity.WaveSupport ActualPrimary.standardRegion
      ActualPrimary.commonGauge.radial.inner ActualPrimary.commonGauge.radial.outer
      (seed B N0).oscillation := by
  apply WaveStateRegularity.fieldSum_support
  intro n l _ theta i x hx hn
  apply ActualPrimaryCoherence.piece_velocity_support ActualPrimary.standardRegion l.2 l.1 n
    (x := (x, theta)) (ActualPrimary.standardRegion.time_pos _ hx)
  intro hz
  exact hn (congrFun hz i)

theorem seed_covariance_regular (B N0 : ℕ) (i j : Fin 3) :
    GaugeDebtIncrement.Regular ActualPrimary.standardRegion
      ActualPrimary.commonGauge.radial.inner ActualPrimary.commonGauge.radial.outer
      ((seed B N0).covariance i j) :=
  WaveStateRegularity.bilinearCovariance_regular ActualPrimary.standardRegion
    (seed_angularSmooth B N0) (seed_angularSmooth B N0) (seed_waveSupport B N0) i j

theorem active_index_le {n : ℕ} {l : Index B N0}
    (hl : l ∈ ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n) :
    CommonWindow.index ActualPrimary.h n ≤
      ChartScales.nativeIndex ActualPrimary.h (BaseChartJets.cellBand l.1) := by
  apply ActualPrimaryCovariance.active_cover_le n
  rw [ActualPrimaryCovariance.activeLabels_product] at hl
  exact (Finset.mem_product.mp hl).1

theorem seed_velocity_periodic (B N0 n : ℕ) (R : ℝ) (s : TorusInverse.Plane) (theta : ℝ) :
    FourierAlias.TorusPeriodic (fun Y => (seed B N0).oscillation n ((R, (s, Y)), theta)) := by
  intro Y k
  funext i
  apply Finset.sum_congr rfl
  intro l hl
  have he := congrFun (ActualPrimaryCoherence.piece_velocity_periodic ActualPrimary.standardRegion
      l.2 l.1 n
    (active_index_le hl) k ((R, (s, Y)), theta)) i
  simp only [ActualPrimaryCoherence.chartDeck, TorusAverages.latticePoint,
    Prod.add_def, add_zero] at he
  exact he

theorem covariance_periodic_of_periodic {U : Set TorusInverse.Plane} {u : Oscillation Point}
    (hu : ∀ n theta i, PhysicalMeanDomain.PeriodicOn U (fun x => u n (x, theta) i))
    (i j : Fin 3) (n : ℕ) : PhysicalMeanDomain.PeriodicOn U (bilinearCovariance u u i j n) := by
  intro R s hs Y k
  change (∫ theta in (0 : ℝ)..2 * Real.pi,
    u n ((R, (s, Y + ((k.1 : ℝ), (k.2 : ℝ)))), theta) i *
      u n ((R, (s, Y + ((k.1 : ℝ), (k.2 : ℝ)))), theta) j) / (2 * Real.pi) =
    (∫ theta in (0 : ℝ)..2 * Real.pi, u n ((R, (s, Y)), theta) i *
      u n ((R, (s, Y)), theta) j) / (2 * Real.pi)
  apply congrArg (fun a : ℝ => a / (2 * Real.pi))
  apply intervalIntegral.integral_congr
  intro theta _
  exact congrArg₂ (· * ·) (hu n theta i R s hs Y k) (hu n theta j R s hs Y k)

theorem seed_covariance_periodic (B N0 : ℕ) (i j : Fin 3) (n : ℕ) :
    PhysicalMeanDomain.PeriodicOn ActualPrimary.standardRegion.carrier
      ((seed B N0).covariance i j n) :=
  covariance_periodic_of_periodic
    (fun n theta i R s _ Y k => congrFun (seed_velocity_periodic B N0 n R s theta Y k) i) i j n

/-- The estimate comes from actual cut amplitudes, curl corrections and
closed slot supports.  Its constants do not count the growing label set. -/
theorem covariance_bounds_of_curl (B N0 : ℕ)
    (hc : LabelSumBounds.UniformWaveClass strip envelope (1 - ChartScales.kappa)
      (fun l : Index B N0 => fun n x =>
        ((primaryPiece l).coefficients.withCutoff (primaryPiece l).cutoff).curlCorrection
          (primaryPiece l).strip (primaryPiece l).directions n (x, 0))) :
    (∀ i j, MeanClass strip 1 ((seed B N0).covariance i j)) ∧
      (∀ i j, MeanClass strip (3 / 2 - ChartScales.kappa)
        ((seed B N0).covariance i j - ActualPrimaryCovariance.tangentCovariance B N0 i j)) := by
  classical
  rcases isEmpty_or_nonempty (Index B N0) with he | he
  · let := he
    have hl (n : ℕ) : ActualPrimary.activeLabels ActualPrimary.standardRegion B N0 n = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr (fun l => isEmptyElim l)
    have hs : (seed B N0).oscillation = 0 := by
      funext n x i
      simp [seed, bandSeed, LabelSumBounds.fieldSum, hl]
    have ht : ActualPrimaryCovariance.tangentSum B N0 = 0 := by
      funext n x i
      simp [ActualPrimaryCovariance.tangentSum, hl]
    have hz (alpha : ℝ) : MeanClass strip alpha (0 : ScalarField Point) :=
      MemClass.zero (fun _ x hx => strip.zeta_nonneg x hx)
    constructor
    · intro i j
      apply MeanIncrementBounds.class_congr (hz 1)
      intro n x _
      simp [State.covariance, hs, bilinearCovariance, angularAverage]
    · intro i j
      apply MeanIncrementBounds.class_congr (hz (3 / 2 - ChartScales.kappa))
      intro n x _
      simp [State.covariance, hs, ActualPrimaryCovariance.tangentCovariance, ht,
        bilinearCovariance, angularAverage]
  · let := he
    exact AssembledPrimary.covariance_bounds ActualPrimary.slots
      (ActualPrimary.activeLabels ActualPrimary.standardRegion B N0)
      (fun _ => ActualPrimaryCovariance.signedLabelOf)
      (fun _ => ActualPrimaryCovariance.signedLabelOf_injective.injOn)
      (fun _ l _ => l.1.val.property.1)
      ActualPrimaryCovariance.physicalWindow ActualPrimaryCovariance.physicalWindow_continuousOn
      ActualPrimaryCovariance.absoluteAuxiliary primaryPiece (baseError B) phase angularMode
      tangent_amplitude_uniform hc (fun l n x _ => envelope_nonneg l n x)
      (fun l n x _ => envelope_le_one l n x) angularMode_ne_zero tangent_amplitude_angle
      exact_amplitude_angle phase_split ActualPrimaryCovariance.piece_support

theorem meanBar_mem {alpha : ℝ} {f : ScalarField Point}
    (hf : MeanIncrementBounds.SmoothOn
      (PhysicalMeanDomain.slowDomain ActualPrimary.standardRegion.carrier) f)
    (hclass : MeanClass strip alpha f) :
    MeanClass strip alpha (StateMomentBalances.meanBar f) :=
  LocalSignedRequest.meanClass_liftedTorusAverage ActualPrimary.standardRegion
    (PrimaryTargetBounds.leftRadius ActualPrimary.nominal)
    (PrimaryTargetBounds.rightRadius ActualPrimary.nominal)
    (FinalSlowBase.edgeExponent ActualPrimary.nominal / 4) 1
    (PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal)
    (div_pos (FinalSlowBase.edgeExponent_pos ActualPrimary.nominal) (by norm_num)) zero_lt_one
    (ChartScales.epsilon ActualPrimary.h) BaseContextAssembly.slowScale
    (ChartScales.epsilon_pos ActualPrimary.h)
    (ChartScales.epsilon_le_one ActualPrimary.h ActualPrimary.outgoing.data.h_pos.le)
    BaseContextAssembly.one_le_slowScale hf hclass

theorem matched_fluxes_of_covariance (B N0 : ℕ)
    (hr : ∀ i j, MeanIncrementBounds.SmoothOn
      (PhysicalMeanDomain.slowDomain ActualPrimary.standardRegion.carrier) ((seed B N0).covariance
          i j))
    (ht : ∀ i j, MeanIncrementBounds.SmoothOn
      (PhysicalMeanDomain.slowDomain ActualPrimary.standardRegion.carrier)
      (ActualPrimaryCovariance.tangentCovariance B N0 i j))
    (hc : ∀ i j, MeanClass strip (3 / 2 - ChartScales.kappa)
      ((seed B N0).covariance i j - ActualPrimaryCovariance.tangentCovariance B N0 i j)) :
    MeanClass strip (3 / 2 - ChartScales.kappa)
      (StateMomentBalances.meanBar ((seed B N0).covariance 0 1) -
        StateMomentBalances.meanBar (ActualPrimary.commonContext B).virtualTheta) ∧
    MeanClass strip (3 / 2 - ChartScales.kappa)
      (StateMomentBalances.meanBar ((seed B N0).covariance 0 2) -
        StateMomentBalances.meanBar (ActualPrimary.commonContext B).virtualAxial) := by
  have hm := ActualPrimaryCovariance.tangent_virtual_bar_meanClass B N0
  have havg (i j : Fin 3) := meanBar_mem ((hr i j).sub (ht i j)) (hc i j)
  constructor
  · apply MeanIncrementBounds.class_congr ((havg 0 1).add
      (hm.1.mono_exponent (by norm_num [ChartScales.kappa] : 3 / 2 - ChartScales.kappa ≤ (2 : ℝ))))
    intro n x hx
    have he := SignedMeanGain.meanBar_sub_on (hr 0 1) (ht 0 1) n
      ((BaseContextAssembly.nativeStrip_mem ActualPrimary.nominal ActualPrimary.standardRegion
          x).mp hx).1
    change _ = StateMomentBalances.meanBar
      ((seed B N0).covariance 0 1 - ActualPrimaryCovariance.tangentCovariance B N0 0 1) n x + _
    rw [he]
    simp only [Pi.sub_apply]
    ring
  · apply MeanIncrementBounds.class_congr ((havg 0 2).add
      (hm.2.mono_exponent (by norm_num [ChartScales.kappa] : 3 / 2 - ChartScales.kappa ≤ (2 : ℝ))))
    intro n x hx
    have he := SignedMeanGain.meanBar_sub_on (hr 0 2) (ht 0 2) n
      ((BaseContextAssembly.nativeStrip_mem ActualPrimary.nominal ActualPrimary.standardRegion
          x).mp hx).1
    change _ = StateMomentBalances.meanBar
      ((seed B N0).covariance 0 2 - ActualPrimaryCovariance.tangentCovariance B N0 0 2) n x + _
    rw [he]
    simp only [Pi.sub_apply]
    ring

end CovarianceInputs

/-! The fixed base and the actual common index supply all the non-primary
fields of the initialization estimates. -/

/-- Primary data, constructed using `MovingInitialization.PrimaryMeanData`. -/
noncomputable def PrimaryData (B N0 : ℕ) : Prop :=
  MovingInitialization.PrimaryMeanData
    (cL := FinalSlowBase.edgeExponent ActualPrimary.nominal / 4) (cR := 1)
    ActualPrimary.standardRegion ActualPrimary.commonGauge
    (PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal)
    (div_pos (FinalSlowBase.edgeExponent_pos ActualPrimary.nominal) (by norm_num)) zero_lt_one
    (ChartScales.epsilon ActualPrimary.h) BaseContextAssembly.slowScale
    (ChartScales.epsilon_pos ActualPrimary.h)
    (ChartScales.epsilon_le_one ActualPrimary.h ActualPrimary.outgoing.data.h_pos.le)
    BaseContextAssembly.one_le_slowScale (ActualPrimary.commonContext B) (seed B N0)

theorem movingSupport_supportedGauge {coord a b : ℝ}
    (U : LocalSignedRequest.SlowRegion coord) {f : Point → ℝ}
    (hs : LocalSignedRequest.MovingSupport a b coord U.carrier f) :
    VariableGaugeMean.SupportedGauge a b (VariableGaugeMean.qLength coord) U.carrier f := by
  intro x hx hn
  have he := hs x hx hn
  have hl := VariableGaugeMean.qLength_pos U.coord_pos U.coord_lt_one (U.time_pos _ hx)
  change a ≤ x.1 / VariableGaugeMean.qLength coord x.2.1 ∧
    x.1 / VariableGaugeMean.qLength coord x.2.1 ≤ b at he
  exact ⟨by simpa only [mul_comm] using (le_div_iff₀ hl).mp he.1,
    by simpa only [mul_comm] using (div_le_iff₀ hl).mp he.2⟩

theorem primaryData_of_covariance (B N0 : ℕ)
    (hc : ∀ i j, MeanClass strip 1 ((seed B N0).covariance i j))
    (hr : ∀ i j, GaugeDebtIncrement.Regular ActualPrimary.standardRegion
      ActualPrimary.commonGauge.radial.inner ActualPrimary.commonGauge.radial.outer
      ((seed B N0).covariance i j))
    (hp : ∀ i j n, PhysicalMeanDomain.PeriodicOn ActualPrimary.standardRegion.carrier
      ((seed B N0).covariance i j n)) : PrimaryData B N0 := by
  have hs := CommonBaseContext.context_stress_properties ActualPrimary.certificate
    ActualPrimary.modulation ActualPrimary.upper B ActualPrimary.standardRegion
    (CommonWindow.index ActualPrimary.h)
  have hsc := CommonBaseContext.context_stress_classes ActualPrimary.certificate
    ActualPrimary.modulation ActualPrimary.upper B ActualPrimary.profile.fullTrueCone
    ActualPrimary.standardRegion (CommonWindow.index ActualPrimary.h)
  refine {
    exponent_pos := ChartScales.radialExponent_pos _ ActualPrimary.outgoing.data.h_pos.le
    gauge_length := ActualPrimary.commonGauge_length
    operators := CommonBaseContext.context_operator_bounds ActualPrimary.certificate
      ActualPrimary.modulation ActualPrimary.upper B ActualPrimary.standardRegion
      (CommonWindow.index_le_native ActualPrimary.h)
    base := CommonBaseContext.context_base_bounds ActualPrimary.certificate
      ActualPrimary.modulation ActualPrimary.upper B ActualPrimary.standardRegion
      (CommonWindow.index ActualPrimary.h)
    localOperators := CommonBaseContext.context_operators_local ActualPrimary.certificate
      ActualPrimary.modulation ActualPrimary.upper B ActualPrimary.standardRegion.carrier
      (CommonWindow.index ActualPrimary.h)
    base_smooth := CommonBaseContext.context_base_smooth ActualPrimary.certificate
      ActualPrimary.modulation ActualPrimary.upper B ActualPrimary.standardRegion
      (CommonWindow.index ActualPrimary.h)
    profile := fun _ _ _ _ => rfl
    mean_zero := rfl
    covariance := hc
    covariance_smooth := fun i j => (hr i j).smooth
    covariance_periodic := hp
    covariance_support := fun i j => (hr i j).supported
    theta := hsc.1
    axial := hsc.2
    theta_smooth := fun n => (hs n).1.fst
    axial_smooth := fun n => (hs n).1.snd
    theta_periodic := fun n => (hs n).2.1
    axial_periodic := fun n => (hs n).2.2.1
    theta_support := fun n => movingSupport_supportedGauge ActualPrimary.standardRegion (hs
        n).2.2.2.1
    axial_support := fun n => movingSupport_supportedGauge ActualPrimary.standardRegion (hs
        n).2.2.2.2 }

theorem initialized_mean_bounds_of_rank (B N0 : ℕ) {sigma : ℝ}
    (htheta : MeanClass strip (1 + sigma) ((ranked B N0).thetaResidual (ActualPrimary.commonContext
        B)))
    (haxial : MeanClass strip (1 + sigma) (fun n x =>
      (ranked B N0).axialResidual (ActualPrimary.commonContext B) n x -
        VariableGaugeMean.temporalAliasState ActualPrimary.commonGauge ActualPrimary.h
          (CommonWindow.index ActualPrimary.h) (ActualPrimary.commonContext B) (primary B N0) n (x,
              0) 2)) :
    MeanResidualBounds strip sigma (ActualPrimary.commonContext B) (initialized B N0) := by
  constructor
  · apply MeanIncrementBounds.class_congr htheta
    intro n x hx
    change (initialized B N0).meanGoodResidual (ActualPrimary.commonContext B) n x 1 = _
    rw [initialized_meanGood B N0 n (BaseContextAssembly.nativeStrip_time
      ActualPrimary.nominal ActualPrimary.standardRegion hx) 1]
    simp [State.reducedMeanResidual, initialAlias, VariableGaugeMean.temporalAliasState,
      VariableGaugeMean.pressureAliasState, initialized, GaugeInitialization.initializedBands,
      GaugeInitialization.retainPressureAlias]
    rfl
  · apply MeanIncrementBounds.class_congr haxial
    intro n x hx
    change (initialized B N0).meanGoodResidual (ActualPrimary.commonContext B) n x 2 = _
    rw [initialized_meanGood B N0 n (BaseContextAssembly.nativeStrip_time
      ActualPrimary.nominal ActualPrimary.standardRegion hx) 2]
    simp [State.reducedMeanResidual, initialAlias, VariableGaugeMean.pressureAliasState,
      initialized, GaugeInitialization.initializedBands, GaugeInitialization.retainPressureAlias]
    rfl

theorem initial_bounds_of_primaryData (B N0 : ℕ) (d : PrimaryData B N0)
    (htheta : MeanClass strip (3 / 2 - ChartScales.kappa)
      (StateMomentBalances.meanBar ((seed B N0).covariance 0 1) -
        StateMomentBalances.meanBar (ActualPrimary.commonContext B).virtualTheta))
    (haxial : MeanClass strip (3 / 2 - ChartScales.kappa)
      (StateMomentBalances.meanBar ((seed B N0).covariance 0 2) -
        StateMomentBalances.meanBar (ActualPrimary.commonContext B).virtualAxial)) :
    CumulativeBounds strip (initialized B N0) ∧
      MeanResidualBounds strip (1 / 5) (ActualPrimary.commonContext B) (initialized B N0) ∧
      DefectBounds slowStrip (1 / 5) (ActualPrimary.commonContext B) (initialized B N0) ∧
      GaugeMassPreservation.ZeroMassesOn ActualPrimary.standardRegion.carrier (initialized B N0) :=
          by
  unfold PrimaryData at d
  have ht := d.temporal_bounds ActualPrimary.outgoing.data.h_pos.le
    (fun n => le_max_right 1 (ChartScales.S n)) (CommonWindow.index ActualPrimary.h)
    (CommonWindow.gap ActualPrimary.h)
    (CommonWindow.native_le_index_add ActualPrimary.h ActualPrimary.outgoing.data.h_pos.le)
    axial rfl (fun _ => rfl) htheta haxial
  have hd := d.temporal_debt_bounds ht
  have hg := ActualPrimary.rank_geometry ActualPrimary.standardRegion B (temporal B N0) hd.smooth
  have hslow := CommonBaseContext.context_isSlow ActualPrimary.certificate ActualPrimary.modulation
    ActualPrimary.upper B ActualPrimary.standardRegion.carrier (CommonWindow.index ActualPrimary.h)
  have hr := d.rank_bounds ht ActualPrimary.rankData hg
    (ActualPrimary.rankData_parameters ActualPrimary.standardRegion.carrier)
    ActualPrimary.rankAmplitude_pos.ne' ActualPrimary.active_left_before_rank
    ActualPrimary.rank_before_active_right rfl hslow.2.1 hslow.2.2
  have hm := initialized_mean_bounds_of_rank B N0
    (hr.theta.mono_exponent (by norm_num : (1 : ℝ) + 1 / 5 ≤ 149 / 100))
    (hr.axial_residual.mono_exponent (by norm_num : (1 : ℝ) + 1 / 5 ≤ 149 / 100))
  exact ⟨⟨hr.cumulative.velocity, hr.cumulative.pressure⟩, hm, hr.defects,
    d.rank_zeroMasses ht ActualPrimary.rankData hg⟩

/-! ## Unconditional bounds for the chosen family -/

theorem curl_amplitude_uniform {B N0 : ℕ} :
    LabelSumBounds.UniformWaveClass strip envelope (1 - ChartScales.kappa)
      (fun l : Index B N0 => fun n x =>
        ((primaryPiece l).coefficients.withCutoff (primaryPiece l).cutoff).curlCorrection
          (primaryPiece l).strip (primaryPiece l).directions n (x, 0)) := by
  have hh := ActualPrimaryBounds.chart_curl_uniform (B := B) (N0 := N0)
  change LabelSumBounds.UniformClass (HarmonicWaveInteraction.productStrip strip)
    (fun l n x => Real.sqrt (strip.zeta x.1) * ActualPrimaryBounds.meanEnvelope l n x.1)
    (1 - ChartScales.kappa) _ at hh
  have hr : LabelSumBounds.UniformWaveClass strip ActualPrimaryBounds.meanEnvelope
      (1 - ChartScales.kappa)
      (fun l : ActualPrimaryBounds.SignedLabel B N0 => fun n x =>
        ((ActualPrimary.chartCoefficients l.1 l.2).withCutoff (ActualPrimary.chartCutoff l.1
            l.2)).curlCorrection
          (HarmonicWaveInteraction.productStrip strip)
          (PrimaryResidualClass.directions (ActualPrimary.commonContext B)) n (x, 0)) :=
    UniformBlockBounds.uniform_slice hh
  exact hr.reindex (fun l : Index B N0 => (l.2, l.1))

theorem covariance_bounds (B N0 : ℕ) :
    (∀ i j, MeanClass strip 1 ((seed B N0).covariance i j)) ∧
      (∀ i j, MeanClass strip (3 / 2 - ChartScales.kappa)
        ((seed B N0).covariance i j - ActualPrimaryCovariance.tangentCovariance B N0 i j)) :=
  covariance_bounds_of_curl B N0 curl_amplitude_uniform

/-- Every field is supplied by the actual primary family and fixed base. -/
theorem primary_mean_data (B N0 : ℕ) : PrimaryData B N0 :=
  primaryData_of_covariance B N0 (covariance_bounds B N0).1
    (seed_covariance_regular B N0) (seed_covariance_periodic B N0)

theorem primary_bounds (B N0 : ℕ) :
    MeanClass strip (1 - ChartScales.kappa) ((primary B N0).gr (ActualPrimary.commonContext B)) ∧
      MeanClass strip (1 - ChartScales.kappa) (primary B N0).pressure ∧
      MeanClass strip (1 - ChartScales.kappa) ((primary B N0).thetaResidual
          (ActualPrimary.commonContext B)) ∧
      MeanClass strip (1 - ChartScales.kappa) ((primary B N0).axialResidual
          (ActualPrimary.commonContext B)) ∧
      CumulativeBounds strip (primary B N0) := by
  have d := primary_mean_data B N0
  unfold PrimaryData at d
  exact MovingInitialization.zeroMean_reconstructed_bounds
    (cL := FinalSlowBase.edgeExponent ActualPrimary.nominal / 4) (cR := 1)
        ActualPrimary.standardRegion
    ActualPrimary.commonGauge (PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal)
    d.exponent_pos (div_pos (FinalSlowBase.edgeExponent_pos ActualPrimary.nominal) (by
        norm_num)) zero_lt_one
    (ChartScales.epsilon ActualPrimary.h) BaseContextAssembly.slowScale
    (ChartScales.epsilon_pos ActualPrimary.h)
    (ChartScales.epsilon_le_one ActualPrimary.h ActualPrimary.outgoing.data.h_pos.le)
    BaseContextAssembly.one_le_slowScale d.gauge_length (ActualPrimary.commonContext B) (seed B N0)
    d.operators d.localOperators d.mean_zero d.covariance d.covariance_smooth d.covariance_support
        d.theta d.axial

theorem matched_fluxes (B N0 : ℕ) :
    MeanClass strip (3 / 2 - ChartScales.kappa)
      (StateMomentBalances.meanBar ((seed B N0).covariance 0 1) -
        StateMomentBalances.meanBar (ActualPrimary.commonContext B).virtualTheta) ∧
    MeanClass strip (3 / 2 - ChartScales.kappa)
      (StateMomentBalances.meanBar ((seed B N0).covariance 0 2) -
        StateMomentBalances.meanBar (ActualPrimary.commonContext B).virtualAxial) :=
  matched_fluxes_of_covariance B N0 (seed_covariance_smooth B N0)
    (tangent_covariance_smooth B N0) (covariance_bounds B N0).2

theorem temporal_bounds (B N0 : ℕ) :
    MovingInitialization.TemporalStateBounds
      (cL := FinalSlowBase.edgeExponent ActualPrimary.nominal / 4) (cR := 1)
      ActualPrimary.standardRegion ActualPrimary.commonGauge
      (PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal)
      (div_pos (FinalSlowBase.edgeExponent_pos ActualPrimary.nominal) (by norm_num)) zero_lt_one
      (ChartScales.epsilon ActualPrimary.h) BaseContextAssembly.slowScale
      (ChartScales.epsilon_pos ActualPrimary.h)
      (ChartScales.epsilon_le_one ActualPrimary.h ActualPrimary.outgoing.data.h_pos.le)
      BaseContextAssembly.one_le_slowScale ActualPrimary.h (CommonWindow.index ActualPrimary.h)
      axial (ActualPrimary.commonContext B) (seed B N0) := by
  have d := primary_mean_data B N0
  unfold PrimaryData at d
  exact d.temporal_bounds ActualPrimary.outgoing.data.h_pos.le
    (fun n => le_max_right 1 (ChartScales.S n)) (CommonWindow.index ActualPrimary.h)
    (CommonWindow.gap ActualPrimary.h)
    (CommonWindow.native_le_index_add ActualPrimary.h ActualPrimary.outgoing.data.h_pos.le)
    axial rfl (fun _ => rfl) (matched_fluxes B N0).1 (matched_fluxes B N0).2

theorem rank_bounds (B N0 : ℕ) :
    MovingInitialization.InitialRankBounds
      (cL := FinalSlowBase.edgeExponent ActualPrimary.nominal / 4) (cR := 1)
      ActualPrimary.standardRegion ActualPrimary.commonGauge
      (PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal)
      (div_pos (FinalSlowBase.edgeExponent_pos ActualPrimary.nominal) (by norm_num)) zero_lt_one
      (ChartScales.epsilon ActualPrimary.h) BaseContextAssembly.slowScale
      (ChartScales.epsilon_pos ActualPrimary.h)
      (ChartScales.epsilon_le_one ActualPrimary.h ActualPrimary.outgoing.data.h_pos.le)
      BaseContextAssembly.one_le_slowScale ActualPrimary.rankData ActualPrimary.h
      (CommonWindow.index ActualPrimary.h) axial (ActualPrimary.commonContext B) (seed B N0) := by
  have d := primary_mean_data B N0
  unfold PrimaryData at d
  have ht := temporal_bounds B N0
  have hg := ActualPrimary.rank_geometry ActualPrimary.standardRegion B (temporal B N0)
    (d.temporal_debt_bounds ht).smooth
  have hslow := CommonBaseContext.context_isSlow ActualPrimary.certificate ActualPrimary.modulation
    ActualPrimary.upper B ActualPrimary.standardRegion.carrier (CommonWindow.index ActualPrimary.h)
  exact d.rank_bounds ht ActualPrimary.rankData hg
    (ActualPrimary.rankData_parameters ActualPrimary.standardRegion.carrier)
    ActualPrimary.rankAmplitude_pos.ne' ActualPrimary.active_left_before_rank
    ActualPrimary.rank_before_active_right rfl hslow.2.1 hslow.2.2

/-- All bands of the literal initialization, with the two aliases retained. -/
theorem initial_bounds (B N0 : ℕ) :
    CumulativeBounds strip (initialized B N0) ∧
      MeanResidualBounds strip (1 / 5) (ActualPrimary.commonContext B) (initialized B N0) ∧
      DefectBounds slowStrip (1 / 5) (ActualPrimary.commonContext B) (initialized B N0) ∧
      GaugeMassPreservation.ZeroMassesOn ActualPrimary.standardRegion.carrier (initialized B N0) :=
  initial_bounds_of_primaryData B N0 (primary_mean_data B N0)
    (matched_fluxes B N0).1 (matched_fluxes B N0).2

theorem initial_cumulative_bounds (B N0 : ℕ) : CumulativeBounds strip (initialized B N0) :=
  (initial_bounds B N0).1

theorem initial_mean_bounds (B N0 : ℕ) :
    MeanResidualBounds strip (1 / 5) (ActualPrimary.commonContext B) (initialized B N0) :=
  (initial_bounds B N0).2.1

theorem initial_debt_bounds (B N0 : ℕ) :
    DefectBounds slowStrip (1 / 5) (ActualPrimary.commonContext B) (initialized B N0) :=
  (initial_bounds B N0).2.2.1

theorem initial_zeroMasses (B N0 : ℕ) :
    GaugeMassPreservation.ZeroMassesOn ActualPrimary.standardRegion.carrier (initialized B N0) :=
  (initial_bounds B N0).2.2.2

theorem initial_mean_smooth (B N0 : ℕ) :
    MeanIncrementBounds.SmoothTriple (PhysicalMeanDomain.slowDomain
        ActualPrimary.standardRegion.carrier)
      (initialized B N0).mean :=
  (rank_bounds B N0).mean_smooth

theorem initial_mean_support (B N0 : ℕ) :
    CorrectionStep.GaugeSupportedTriple ActualPrimary.commonGauge.radial.inner
        ActualPrimary.commonGauge.radial.outer
      (VariableGaugeMean.qLength (2 * ActualPrimary.h)) ActualPrimary.standardRegion.carrier
      (initialized B N0).mean :=
  (rank_bounds B N0).mean_support

theorem initialized_formula (B N0 : ℕ) :
    initialized B N0 = GaugeInitialization.initializedBands ActualPrimary.commonGauge
        ActualPrimary.rankData
      ActualPrimary.h (CommonWindow.index ActualPrimary.h) ((0, 1), 0) (ActualPrimary.commonContext
          B)
      (ActualPrimary.activeLabels ActualPrimary.standardRegion B N0)
      (fun l => ActualPrimary.piece ActualPrimary.standardRegion l.2 l.1)
      (ActualBaseResidual.baseError ActualPrimary.certificate ActualPrimary.modulation
          ActualPrimary.upper B) := rfl

end NavierStokes.ActualInitialMean

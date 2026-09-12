/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SlowBaseEndpoint
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPrimaryDynamics
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualGaussianCoverage
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualInitialCoherence
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPhaseJetBounds
import LeanPool.NavierStokesAndEuler.NavierStokes.GaugeExcludedBounds
import LeanPool.NavierStokesAndEuler.NavierStokes.ResidualRegularity
import LeanPool.NavierStokesAndEuler.NavierStokes.UniformBlockBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualBaseResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPrimaryBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPrimaryCovariance
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPrimaryCoherence

/-!
# Excluded errors of the actual initialized state

The base term is the normalized residual of the same fixed slow base.
The primary Gaussian and current gauge aliases are retained literally.
-/

section

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

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.ActualInitialExcluded

open Set Filter Function WeightedClasses ProblemStatement
open scoped Topology ContDiff BigOperators

section BaseContinuation

theorem radialDivergence_contDiffAt {f : SimilarityProfile.PhysicalProfile}
    {p : SimilarityProfile.PhysicalPoint} (hf : ContDiffAt ℝ ∞ f p)
    (hs : 0 < p.2.1) (k : ℝ) :
    ContDiffAt ℝ ∞ (LeadingStress.radialDivergence k f) p := by
  have hr : ContDiffAt ℝ ∞ (fun p : SimilarityProfile.PhysicalPoint =>
      Real.sqrt (2 * p.2.1)) p :=
    (contDiffAt_const.mul contDiffAt_snd.fst).sqrt (by positivity)
  have hd : ContDiffAt ℝ ∞ (SimilarityProfile.partialS f) p :=
    (hf.fderiv_right (by simp)).clm_apply contDiffAt_const
  exact (hr.mul hd).add ((contDiffAt_const.mul hf).div hr (by positivity))

theorem stressForce_contDiffAt {f g : SimilarityProfile.PhysicalProfile}
    {z : SpaceTime}
    (hf : ContDiffAt ℝ ∞ f (AxisymmetricFields.profilePoint z.1 z.2))
    (hg : ContDiffAt ℝ ∞ g (AxisymmetricFields.profilePoint z.1 z.2))
    (hr : 0 < AxisymmetricFields.radialEnergy z.2) :
    ContDiffAt ℝ ∞ (BaseResidual.stressForce f g) z := by
  have hp := AxisymmetricFields.contDiff_profilePoint.contDiffAt (x := z) (n := ∞)
  have hR : ContDiffAt ℝ ∞ (fun z : SpaceTime =>
      Real.sqrt (2 * AxisymmetricFields.radialEnergy z.2)) z :=
    (contDiffAt_const.mul (AxisymmetricFields.contDiff_radialEnergy.contDiffAt.comp z
      contDiffAt_snd)).sqrt (by positivity)
  have hf' := (radialDivergence_contDiffAt hf hr 2).comp z hp
  have hg' := (radialDivergence_contDiffAt hg hr 1).comp z hp
  have hx (i : Fin 3) : ContDiffAt ℝ ∞ (fun z : SpaceTime => z.2 i) z :=
    (AxisymmetricFields.projection i).contDiff.contDiffAt.comp z contDiffAt_snd
  exact (((hx 1).div hR (by positivity)).mul hf').smul contDiffAt_const |>.add
    (((((hx 0).neg).div hR (by positivity)).mul hf').smul contDiffAt_const) |>.add
      (hg'.neg.smul contDiffAt_const)

theorem stressForce_congr {f g f' g' : SimilarityProfile.PhysicalProfile}
    {z : SpaceTime}
    (hf : f =ᶠ[𝓝 (AxisymmetricFields.profilePoint z.1 z.2)] f')
    (hg : g =ᶠ[𝓝 (AxisymmetricFields.profilePoint z.1 z.2)] g') :
    BaseResidual.stressForce f g z = BaseResidual.stressForce f' g' z := by
  simp only [BaseResidual.stressForce, SlowResidualMatching.tangentialStressForce,
    LeadingStress.radialDivergence, SimilarityProfile.partialS,
    hf.self_of_nhds, hg.self_of_nhds, hf.fderiv_eq, hg.fderiv_eq]

/-- Continuation domain, given by `EndpointCoordinates.cartesianDomain h ∩ {z | 0 <
AxisymmetricFields.radialEnergy z.2}`. -/
noncomputable def continuationDomain (h : ℝ) : Set SpaceTime :=
  EndpointCoordinates.cartesianDomain h ∩ {z | 0 < AxisymmetricFields.radialEnergy z.2}

theorem continuationDomain_open (h : ℝ) : IsOpen (continuationDomain h) :=
  (EndpointCoordinates.cartesianDomain_open h).inter
    (isOpen_lt continuous_const ((AxisymmetricFields.contDiff_radialEnergy (n := 0)).continuous.comp
      continuous_snd))

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld) (upper : ℝ) (B : ℕ)

/-- The original profiles and original scale schedule continued through
the regular endpoint coordinates. -/
noncomputable def baseErrorContinuation : SpaceTime → Space :=
  let a := FinalSlowBase.scales H v upper B
  let d := FinalSlowBase.coefficients H v
  fun z => navierStokesResidual
    (SlowBaseEndpoint.velocityExtension a F.data.h W.axis.normalization d)
    (SlowBaseEndpoint.pressureExtension a F.data.h W.axis.normalization d) z.1 z.2 -
      BaseResidual.stressForce
        (SlowBaseEndpoint.profileExtension a F.data.h (-CoordinateAlgebra.A F.data.h - 1 / 2)
          (SlowBorelBase.bundleComponent W.axis.normalization d 3))
        (SlowBaseEndpoint.profileExtension a F.data.h (-CoordinateAlgebra.A F.data.h - 1 / 2)
          (SlowBorelBase.bundleComponent W.axis.normalization d 4)) z

theorem baseErrorContinuation_smooth :
    ContDiffOn ℝ ∞ (baseErrorContinuation H v upper B) (continuationDomain F.data.h) := by
  have ha := FinalSlowBase.scales_strictMono H v upper B
  have hd := FinalSlowBase.coefficients_smooth H v
  have hu := SlowBaseEndpoint.velocityExtension_smoothOn ha F.data.h_pos F.data.h_lt_half
    hd W.axis.normalization
  have hp := SlowBaseEndpoint.pressureExtension_smoothOn ha F.data.h_pos F.data.h_lt_half
    hd W.axis.normalization
  have hres := ResidualRegularity.contDiffOn_residual (continuationDomain_open F.data.h)
    (hu.mono inter_subset_left) (hp.mono inter_subset_left)
  apply hres.sub
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  exact stressForce_contDiffAt
    (SlowBaseEndpoint.profileExtension_smoothAt ha F.data.h_pos F.data.h_lt_half
      (SlowBorelBase.bundleComponent_smooth hd W.axis.normalization 3) _ hz.1)
    (SlowBaseEndpoint.profileExtension_smoothAt ha F.data.h_pos F.data.h_lt_half
      (SlowBorelBase.bundleComponent_smooth hd W.axis.normalization 4) _ hz.1) hz.2

theorem baseErrorContinuation_eq {z : SpaceTime} (hz : z.1 < 1) :
    baseErrorContinuation H v upper B z = FinalSlowBase.error H v upper B z := by
  have hu := SlowBaseEndpoint.velocityExtension_eventuallyEq
    (FinalSlowBase.scales H v upper B) F.data.h_pos F.data.h_lt_half W.axis.normalization
    (FinalSlowBase.coefficients H v) hz
  have hp := SlowBaseEndpoint.pressureExtension_eventuallyEq
    (FinalSlowBase.scales H v upper B) F.data.h_pos F.data.h_lt_half W.axis.normalization
    (FinalSlowBase.coefficients H v) hz
  have hres := ResidualRegularity.residual_congr hu hp
  have ht := SlowBaseEndpoint.profileExtension_eventuallyEq
    (FinalSlowBase.scales H v upper B) F.data.h_pos F.data.h_lt_half
    (-CoordinateAlgebra.A F.data.h - 1 / 2)
    (SlowBorelBase.bundleComponent W.axis.normalization (FinalSlowBase.coefficients H v) 3)
    (p := AxisymmetricFields.profilePoint z.1 z.2) hz
  have hax := SlowBaseEndpoint.profileExtension_eventuallyEq
    (FinalSlowBase.scales H v upper B) F.data.h_pos F.data.h_lt_half
    (-CoordinateAlgebra.A F.data.h - 1 / 2)
    (SlowBorelBase.bundleComponent W.axis.normalization (FinalSlowBase.coefficients H v) 4)
    (p := AxisymmetricFields.profilePoint z.1 z.2) hz
  exact congrArg₂ (· - ·) hres (stressForce_congr ht hax)

theorem baseErrorContinuation_germ {z : SpaceTime} (hz : z.1 < 1) :
    baseErrorContinuation H v upper B =ᶠ[𝓝 z] FinalSlowBase.error H v upper B := by
  filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hz] with y hy
  exact baseErrorContinuation_eq H v upper B hy

end BaseContinuation

section CompactNativeGeometry

/-- Slow: an abbreviation for `PhaseCalculus.Slow`. -/
abbrev Slow := PhaseCalculus.Slow

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
  (U : LocalSignedRequest.SlowRegion (2 * F.data.h))

/-- A compact closed set containing the native slow region. Its last
inequality retains separation from the simultaneous time/axial origin. -/
noncomputable def closedSlowSet : Set Slow :=
  Metric.closedBall 0 (BaseContextAssembly.geometryBound W U) ∩
    {p | BaseContextAssembly.geometryRadius W U ≤ p.1 ∧ 0 ≤ p.2.2 ∧
      U.qlo ≤ p.2.2 + p.2.1 ^ 2 * (max 1 U.qhi) ^ (2 * F.data.h)}

theorem closedSlowSet_compact : IsCompact (closedSlowSet W U) := by
  apply (isCompact_closedBall _ _).inter_right
  exact (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_const continuous_snd.snd).inter
      (isClosed_le continuous_const
        (continuous_snd.snd.add ((continuous_snd.fst.pow 2).mul continuous_const))))

theorem slowCarrier_subset_closedSlowSet :
    BaseContextAssembly.slowCarrier W U ⊆ closedSlowSet W U := by
  intro p hp
  have hg := BaseContextAssembly.native_geometry W U ℕ
  have hT := hg.time 0 p hp
  have hq := U.q_mem (p.2.2, p.2.1)
    ((BaseContextAssembly.nativeStrip_mem W U _).mp hp).1
  have hs := SimilarityCoordinates.coordinateQ_spec U.coord_pos U.coord_lt_one
    (p := (p.2.2, p.2.1)) hT
  have hpow := Real.rpow_le_rpow hs.1.le (hq.2.trans (le_max_right (1 : ℝ) U.qhi))
    U.coord_pos.le
  refine ⟨?_, hg.radius 0 p hp, hT.le, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hg.bounded 0 p hp
  · have hm := mul_le_mul_of_nonneg_left hpow (sq_nonneg p.2.1)
    dsimp only [SimilarityCoordinates.forwardScalar] at hs
    linarith [hq.1, hs.2]

theorem closedSlowSet_radius {p : Slow} (hp : p ∈ closedSlowSet W U) : 0 < p.1 :=
  (BaseContextAssembly.geometryRadius_pos W U).trans_le hp.2.1

theorem closedSlowSet_axial_ne {p : Slow} (hp : p ∈ closedSlowSet W U)
    (hT : p.2.2 = 0) : p.2.1 ≠ 0 := by
  intro hz
  have hsep := hp.2.2.2
  rw [hT, hz, zero_pow (by decide : 2 ≠ 0), zero_mul, zero_add] at hsep
  exact (not_le_of_gt U.qlo_pos) hsep

/-- Band linear as an element of `Slow →L[ℝ] SpaceTime`. -/
noncomputable def bandLinear (h Q : ℝ) : Slow →L[ℝ] SpaceTime :=
  ((-Q) • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).prod
    (AxisymmetricResidual.packDerivative
      ((Real.sqrt Q) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) 0
      ((Q ^ CoordinateAlgebra.D h) •
        (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))

theorem bandPoint_affine (h Q : ℝ) (p : Slow) :
    BaseChartJets.bandPoint h Q p = bandLinear h Q p + (1, 0) := by
  apply Prod.ext
  · change 1 - Q * p.2.2 = -Q * p.2.2 + 1
    ring
  · ext i
    fin_cases i <;>
      simp [BaseChartJets.bandPoint, bandLinear, AxisymmetricResidual.packDerivative,
          coordinateVector]

theorem bandPoint_smooth (h Q : ℝ) : ContDiff ℝ ∞ (BaseChartJets.bandPoint h Q) := by
  have he : BaseChartJets.bandPoint h Q = fun p => bandLinear h Q p + (1, 0) :=
    funext (bandPoint_affine h Q)
  rw [he]
  exact (bandLinear h Q).contDiff.add contDiff_const

theorem bandPoint_closed_mem {Q : ℝ} (hQ : 0 < Q) {p : Slow}
    (hp : p ∈ closedSlowSet W U) :
    BaseChartJets.bandPoint F.data.h Q p ∈ continuationDomain F.data.h := by
  have hr := closedSlowSet_radius W U hp
  constructor
  · rcases eq_or_lt_of_le hp.2.2.1 with hT | hT
    · have hz : (BaseChartJets.bandPoint F.data.h Q p).2 2 ≠ 0 := by
        change Q ^ CoordinateAlgebra.D F.data.h * p.2.1 ≠ 0
        exact mul_ne_zero (Real.rpow_pos_of_pos hQ _).ne'
          (closedSlowSet_axial_ne W U hp hT.symm)
      have ht : (BaseChartJets.bandPoint F.data.h Q p).1 = 1 := by
        simp only [BaseChartJets.bandPoint, ← hT, mul_zero, sub_zero]
      rw [← Prod.eta (BaseChartJets.bandPoint F.data.h Q p), ht]
      exact EndpointCoordinates.cartesian_endpoint_mem F.data.h_pos F.data.h_lt_half hz
    · exact EndpointCoordinates.past_mem_domain F.data.h_pos F.data.h_lt_half
        (BaseChartJets.bandPoint_time (h := F.data.h) hQ hT)
  · change 0 < ((Real.sqrt Q * p.1) ^ 2 + 0 ^ 2) / 2
    have hh : 0 < Real.sqrt Q * p.1 := mul_pos (Real.sqrt_pos.mpr hQ) hr
    positivity

end CompactNativeGeometry

section PhysicalBaseJets

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
  (U : LocalSignedRequest.SlowRegion (2 * F.data.h))

theorem bandLinear_bound {h Q : ℝ} (hQ : 0 < Q) (hQone : Q ≤ 1)
    (hD : 0 ≤ CoordinateAlgebra.D h) : ‖bandLinear h Q‖ ≤ 4 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro p
  have hs : 0 ≤ Real.sqrt Q := Real.sqrt_nonneg Q
  have hsone : Real.sqrt Q ≤ 1 := Real.sqrt_le_one.mpr hQone
  have hd : 0 ≤ Q ^ CoordinateAlgebra.D h := Real.rpow_nonneg hQ.le _
  have hdone : Q ^ CoordinateAlgebra.D h ≤ 1 := Real.rpow_le_one hQ.le hQone hD
  have hT : |Q * p.2.2| ≤ ‖p‖ := by
    rw [abs_mul, abs_of_pos hQ]
    exact (mul_le_of_le_one_left (abs_nonneg _) hQone).trans
      ((norm_snd_le p.2).trans (norm_snd_le p))
  have hR : |Real.sqrt Q * p.1| ≤ ‖p‖ := by
    rw [abs_mul, abs_of_nonneg hs]
    exact (mul_le_of_le_one_left (abs_nonneg _) hsone).trans (norm_fst_le p)
  have hZ : |Q ^ CoordinateAlgebra.D h * p.2.1| ≤ ‖p‖ := by
    rw [abs_mul, abs_of_nonneg hd]
    exact (mul_le_of_le_one_left (abs_nonneg _) hdone).trans
      ((norm_fst_le p.2).trans (norm_snd_le p))
  change max ‖-Q * p.2.2‖ ‖AxisymmetricResidual.pack
    (Real.sqrt Q * p.1) 0 (Q ^ CoordinateAlgebra.D h * p.2.1)‖ ≤ _
  apply max_le
  · have hn : ‖-Q * p.2.2‖ = |Q * p.2.2| := by simp [Real.norm_eq_abs, abs_mul]
    rw [hn]
    linarith [norm_nonneg p]
  · have hh := PhaseEstimates.vec3_norm_le_sum
      (AxisymmetricResidual.pack (Real.sqrt Q * p.1) 0 (Q ^ CoordinateAlgebra.D h * p.2.1))
    simp only [AxisymmetricResidual.pack_zero, AxisymmetricResidual.pack_one,
      AxisymmetricResidual.pack_two, abs_zero, add_zero] at hh
    linarith [norm_nonneg p]

theorem Q_tendsto_zero : Tendsto ChartScales.Q atTop (𝓝 0) := by
  simpa only [ChartScales.epsilon, Real.rpow_zero, Real.rpow_one, one_mul] using
    ChartScales.slow_power_epsilon_tendsto_zero (h := 1) (by norm_num) 0 1 (by norm_num)

/-- Native approach filter, constructed using `Filter.map`. -/
noncomputable def nativeApproachFilter : Filter SpaceTime :=
  Filter.map (fun p : ℕ × Slow => BaseChartJets.bandPoint F.data.h (ChartScales.Q p.1) p.2)
    (atTop ×ˢ 𝓟 (BaseContextAssembly.slowCarrier W U))

theorem nativeApproach_q_bound {n : ℕ} {p : Slow}
    (hp : p ∈ BaseContextAssembly.slowCarrier W U) :
    0 < (SlowBorelBase.cartesianChart F.data.h
      (BaseChartJets.bandPoint F.data.h (ChartScales.Q n) p)).1 ∧
    (SlowBorelBase.cartesianChart F.data.h
      (BaseChartJets.bandPoint F.data.h (ChartScales.Q n) p)).1 ≤ ChartScales.Q n * U.qhi := by
  have ht := (BaseContextAssembly.native_geometry W U ℕ).time 0 p hp
  rw [BaseChartJets.bandPoint_chart F.data.h_pos F.data.h_lt_half (ChartScales.Q_pos n) ht]
  have hq := U.q_mem (p.2.2, p.2.1)
    ((BaseContextAssembly.nativeStrip_mem W U _).mp hp).1
  have he : (BaseChartJets.normalizedCoordinates F.data.h p).1 =
      SimilarityCoordinates.coordinateQ (2 * F.data.h) (p.2.2, p.2.1) := by
    rw [BaseChartJets.normalizedCoordinates_eq]
    rfl
  change 0 < ChartScales.Q n * (BaseChartJets.normalizedCoordinates F.data.h p).1 ∧
    ChartScales.Q n * (BaseChartJets.normalizedCoordinates F.data.h p).1 ≤ ChartScales.Q n * U.qhi
  rw [he]
  constructor
  · exact mul_pos (ChartScales.Q_pos n) (U.qlo_pos.trans_le hq.1)
  · exact mul_le_mul_of_nonneg_left hq.2 (ChartScales.Q_pos n).le

/-- Native approach, bundling `carrier`, `compact`, `in_carrier`, `exact` and the required
compatibility proofs. -/
noncomputable def nativeApproach : BaseResidual.PhysicalApproach
    (nativeApproachFilter W U) F.data.h 0
      (NominalConeAssembly.activeRight W) where
  carrier := Metric.closedBall 0 (1 + 4 * BaseContextAssembly.geometryBound W U)
  compact := isCompact_closedBall _ _
  in_carrier := by
    rw [nativeApproachFilter, Filter.eventually_map, Filter.eventually_prod_principal_iff]
    exact Filter.Eventually.of_forall (fun n p hp => by
      rw [Metric.mem_closedBall, dist_zero_right, bandPoint_affine]
      have hD : 0 ≤ CoordinateAlgebra.D F.data.h := by
        unfold CoordinateAlgebra.D; linarith [F.data.h_lt_half]
      have hb := (bandLinear_bound (ChartScales.Q_pos n) (ChartScales.Q_le_one n) hD)
      have hn := (BaseContextAssembly.native_geometry W U ℕ).bounded 0 p hp
      have he := (bandLinear F.data.h (ChartScales.Q n)).le_opNorm p
      calc
        _ ≤ ‖bandLinear F.data.h (ChartScales.Q n) p‖ + ‖((1 : ℝ), (0 : Space))‖ := norm_add_le _ _
        _ ≤ 4 * ‖p‖ + 1 := by
          have hx := he.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg p))
          simpa using add_le_add_left hx 1
        _ ≤ _ := by linarith)
  past := by
    rw [nativeApproachFilter, Filter.eventually_map, Filter.eventually_prod_principal_iff]
    exact Filter.Eventually.of_forall (fun n p hp =>
      BaseChartJets.bandPoint_time (h := F.data.h) (ChartScales.Q_pos n)
        ((BaseContextAssembly.native_geometry W U ℕ).time 0 p hp))
  radial := by
    rw [nativeApproachFilter, Filter.eventually_map, Filter.eventually_prod_principal_iff]
    exact Filter.Eventually.of_forall (fun n p hp => by
      rw [BaseChartJets.bandPoint_chart F.data.h_pos F.data.h_lt_half (ChartScales.Q_pos n)
        ((BaseContextAssembly.native_geometry W U ℕ).time 0 p hp)]
      exact ⟨(NominalConeAssembly.activeLeft_pos W).le.trans
          ((BaseContextAssembly.native_geometry W U ℕ).x_range 0 p hp).1.le,
        ((BaseContextAssembly.native_geometry W U ℕ).x_range 0 p hp).2.le⟩)
  scale := by
    rw [nativeApproachFilter, tendsto_map'_iff]
    have hupper : Tendsto (fun p : ℕ × Slow => ChartScales.Q p.1 * U.qhi)
        (atTop ×ˢ 𝓟 (BaseContextAssembly.slowCarrier W U)) (𝓝 0) := by
      simpa only [zero_mul, Function.comp_def] using (Q_tendsto_zero.mul_const U.qhi).comp
          tendsto_fst
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    · rw [Filter.eventually_prod_principal_iff]
      exact Filter.Eventually.of_forall (fun n p hp => (nativeApproach_q_bound W U hp).1.le)
    · rw [Filter.eventually_prod_principal_iff]
      exact Filter.Eventually.of_forall (fun n p hp => (nativeApproach_q_bound W U hp).2)

variable (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld) (upper : ℝ) (B : ℕ)

theorem physical_error_eventual (m : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ p ∈ BaseContextAssembly.slowCarrier W U,
      ‖iteratedFDeriv ℝ m (FinalSlowBase.error H v upper B)
        (BaseChartJets.bandPoint F.data.h (ChartScales.Q n) p)‖ ≤ C * ChartScales.Q n ^ r := by
  obtain ⟨C, hC, hb⟩ := FinalSlowBase.error_jetRate H v upper B (nativeApproach W U)
    (le_max_right _ _) m r hr
  rw [nativeApproachFilter, Filter.eventually_map, Filter.eventually_prod_principal_iff] at hb
  refine ⟨C * (max 1 U.qhi) ^ r, mul_nonneg hC (Real.rpow_nonneg (le_max_left _ _ |>.trans'
      zero_le_one) _), ?_⟩
  filter_upwards [hb] with n hn
  intro p hp
  have hq := nativeApproach_q_bound W U (n := n) hp
  have hbig : (SlowBorelBase.cartesianChart F.data.h
      (BaseChartJets.bandPoint F.data.h (ChartScales.Q n) p)).1 ≤
        ChartScales.Q n * max 1 U.qhi :=
    hq.2.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (ChartScales.Q_pos n).le)
  calc
    _ ≤ C * (SlowBorelBase.cartesianChart F.data.h
        (BaseChartJets.bandPoint F.data.h (ChartScales.Q n) p)).1 ^ r := hn p hp
    _ ≤ C * (ChartScales.Q n * max 1 U.qhi) ^ r :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hq.1.le hbig hr) hC
    _ = _ := by rw [Real.mul_rpow (ChartScales.Q_pos n).le (by positivity)]; ring

/-- Fixed bands include the nonzero-axial terminal boundary. Their
compact bound comes from the actual continuation, not an open-past box. -/
theorem physical_error_fixed (n m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p ∈ BaseContextAssembly.slowCarrier W U,
      ‖iteratedFDeriv ℝ m (FinalSlowBase.error H v upper B)
        (BaseChartJets.bandPoint F.data.h (ChartScales.Q n) p)‖ ≤ C := by
  let K := BaseChartJets.bandPoint F.data.h (ChartScales.Q n) '' closedSlowSet W U
  have hK : IsCompact K := (closedSlowSet_compact W U).image (bandPoint_smooth _ _).continuous
  have hKU : K ⊆ continuationDomain F.data.h := by
    rintro _ ⟨p, hp, rfl⟩
    exact bandPoint_closed_mem W U (ChartScales.Q_pos n) hp
  obtain ⟨C, hC, hb⟩ := PhaseJetBounds.compact_jet_bound (continuationDomain_open F.data.h)
    (baseErrorContinuation_smooth H v upper B) hK hKU m
  refine ⟨C, hC, fun p hp => ?_⟩
  have he := SolenoidalDiagonal.iteratedFDeriv_eventuallyEq
    (baseErrorContinuation_germ H v upper B
      (BaseChartJets.bandPoint_time (h := F.data.h) (ChartScales.Q_pos n)
        ((BaseContextAssembly.native_geometry W U ℕ).time 0 p hp))) m
  rw [← he.self_of_nhds]
  exact hb m le_rfl _ ⟨p, slowCarrier_subset_closedSlowSet W U hp, rfl⟩

theorem physical_error_jet_bound (m : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n p, p ∈ BaseContextAssembly.slowCarrier W U →
      ‖iteratedFDeriv ℝ m (FinalSlowBase.error H v upper B)
        (BaseChartJets.bandPoint F.data.h (ChartScales.Q n) p)‖ ≤ C * ChartScales.Q n ^ r := by
  classical
  obtain ⟨C, hC, hb⟩ := physical_error_eventual W U H v upper B m r hr
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hb
  choose A hA hAb using fun n => physical_error_fixed W U H v upper B n m
  let D := ∑ n ∈ Finset.range N, A n / ChartScales.Q n ^ r
  have hterm (n : ℕ) : 0 ≤ A n / ChartScales.Q n ^ r :=
    div_nonneg (zero_le_one.trans (hA n)) (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _).le
  have hD : 0 ≤ D := Finset.sum_nonneg (fun n _ => hterm n)
  refine ⟨C + D, add_nonneg hC hD, fun n p hp => ?_⟩
  have hq : 0 < ChartScales.Q n ^ r := Real.rpow_pos_of_pos (ChartScales.Q_pos n) _
  by_cases hn : N ≤ n
  · exact (hN n hn p hp).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) hq.le)
  · have hAn : A n / ChartScales.Q n ^ r ≤ D :=
      Finset.single_le_sum (fun k _ => hterm k) (Finset.mem_range.mpr (lt_of_not_ge hn))
    have hm := mul_le_mul_of_nonneg_right (hAn.trans (le_add_of_nonneg_left hC)) hq.le
    rw [div_mul_cancel₀ _ hq.ne'] at hm
    exact (hAb n p hp).trans hm

theorem physical_error_prefix_bound (m : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n p, p ∈ BaseContextAssembly.slowCarrier W U → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (FinalSlowBase.error H v upper B)
        (BaseChartJets.bandPoint F.data.h (ChartScales.Q n) p)‖ ≤ C * ChartScales.Q n ^ r := by
  classical
  choose A hA hAb using fun j => physical_error_jet_bound W U H v upper B j r hr
  refine ⟨∑ j ∈ Finset.range (m + 1), A j, Finset.sum_nonneg (fun j _ => hA j), ?_⟩
  intro n p hp j hj
  exact (hAb j n p hp).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun k _ => hA k) (Finset.mem_range.mpr (by omega)))
      (Real.rpow_pos_of_pos (ChartScales.Q_pos n) _).le)

end PhysicalBaseJets

section NormalizedBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld) (upper : ℝ) (B : ℕ)
  (U : LocalSignedRequest.SlowRegion (2 * F.data.h))

/-- Normalized base, constructed using `ChartScales.Q`. -/
noncomputable def normalizedBase (n : ℕ) (p : Slow) : Space :=
  ChartScales.Q n ^ (2 * CoordinateAlgebra.A F.data.h + 1 / 2) •
    FinalSlowBase.error H v upper B (BaseChartJets.bandPoint F.data.h (ChartScales.Q n) p)

theorem normalizedBase_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ (normalizedBase H v upper B n) (BaseContextAssembly.slowCarrier W U) := by
  apply contDiffOn_const.fun_smul
  apply (FinalSlowBase.error_smooth H v upper B).comp (bandPoint_smooth _ _).contDiffOn
  intro p hp
  exact ⟨BaseChartJets.bandPoint_time (h := F.data.h) (ChartScales.Q_pos n)
    ((BaseContextAssembly.native_geometry W U ℕ).time 0 p hp), Set.mem_univ _⟩

theorem normalizedBase_prefix (alpha : ℝ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n p, p ∈ BaseContextAssembly.slowCarrier W U → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (normalizedBase H v upper B n) p‖ ≤
        C * ChartScales.epsilon F.data.h n ^ alpha := by
  let a := 2 * CoordinateAlgebra.A F.data.h + 1 / 2
  let r := max 0 (F.data.h * alpha - a)
  have hr : 0 ≤ r := le_max_left _ _
  have hexp : F.data.h * alpha ≤ a + r := by
    have hh : F.data.h * alpha - a ≤ r := le_max_right _ _
    linarith
  obtain ⟨C, hC, hb⟩ := physical_error_prefix_bound W U H v upper B m r hr
  refine ⟨C * 4 ^ m, mul_nonneg hC (by positivity), fun n p hp j hj => ?_⟩
  have ht := (BaseContextAssembly.native_geometry W U ℕ).time 0 p hp
  have he : ContDiffAt ℝ ∞
      (fun p => FinalSlowBase.error H v upper B (BaseChartJets.bandPoint F.data.h (ChartScales.Q n)
          p)) p :=
    ((FinalSlowBase.error_smooth H v upper B).contDiffAt
      (BaseResidual.past_isOpen.mem_nhds
        ⟨BaseChartJets.bandPoint_time (h := F.data.h) (ChartScales.Q_pos n) ht, Set.mem_univ
            _⟩)).comp p
      (bandPoint_smooth _ _).contDiffAt
  have hcomp := PhaseJetBounds.norm_jet_comp_affine BaseResidual.past_isOpen
    (FinalSlowBase.error_smooth H v upper B) (bandLinear F.data.h (ChartScales.Q n)) (1, 0)
    (x := p) (by simpa only [← bandPoint_affine] using
      (show BaseChartJets.bandPoint F.data.h (ChartScales.Q n) p ∈ BaseResidual.past from
        ⟨BaseChartJets.bandPoint_time (h := F.data.h) (ChartScales.Q_pos n) ht, Set.mem_univ _⟩)) j
  simp only [← bandPoint_affine] at hcomp
  have hD : 0 ≤ CoordinateAlgebra.D F.data.h := by
    unfold CoordinateAlgebra.D; linarith [F.data.h_lt_half]
  have hnorm : ‖bandLinear F.data.h (ChartScales.Q n)‖ ^ j ≤ 4 ^ m :=
    (pow_le_pow_left₀ (norm_nonneg _)
      (bandLinear_bound (ChartScales.Q_pos n) (ChartScales.Q_le_one n) hD) j).trans
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hj)
  change ‖iteratedFDeriv ℝ j (fun p => ChartScales.Q n ^ a •
    FinalSlowBase.error H v upper B (BaseChartJets.bandPoint F.data.h (ChartScales.Q n) p)) p‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply'
    (he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl j))]
  have hnsmul := norm_smul (ChartScales.Q n ^ a : ℝ)
    (iteratedFDeriv ℝ j (fun p => FinalSlowBase.error H v upper B
      (BaseChartJets.bandPoint F.data.h (ChartScales.Q n) p)) p)
  rw [hnsmul,
    Real.norm_of_nonneg (Real.rpow_pos_of_pos (ChartScales.Q_pos n) a).le]
  calc
    _ ≤ ChartScales.Q n ^ a *
        (‖iteratedFDeriv ℝ j (FinalSlowBase.error H v upper B)
          (BaseChartJets.bandPoint F.data.h (ChartScales.Q n) p)‖ *
            ‖bandLinear F.data.h (ChartScales.Q n)‖ ^ j) :=
      mul_le_mul_of_nonneg_left hcomp (Real.rpow_pos_of_pos (ChartScales.Q_pos n) a).le
    _ ≤ ChartScales.Q n ^ a * (C * ChartScales.Q n ^ r * 4 ^ m) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (hb n p hp j hj) hnorm (by positivity)
        (mul_nonneg hC (Real.rpow_pos_of_pos (ChartScales.Q_pos n) r).le))
        (Real.rpow_pos_of_pos (ChartScales.Q_pos n) a).le
    _ = (C * 4 ^ m) * ChartScales.Q n ^ (a + r) := by
      rw [Real.rpow_add (ChartScales.Q_pos n) a r]; ring
    _ ≤ (C * 4 ^ m) * ChartScales.epsilon F.data.h n ^ alpha := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (by positivity))
      rw [ChartScales.epsilon, ← Real.rpow_mul (ChartScales.Q_pos n).le]
      exact Real.rpow_le_rpow_of_exponent_ge (ChartScales.Q_pos n) (ChartScales.Q_le_one n) hexp

theorem normalizedBase_envelope (alpha : ℝ) :
    PrimaryPulseBounds.EnvelopeJets (BaseChartJets.unitScale (BaseContextAssembly.phaseDomain W U
        ℕ))
      (fun n _ => ChartScales.epsilon F.data.h n ^ alpha) (normalizedBase H v upper B) := by
  refine ⟨fun n _ _ => (Real.rpow_pos_of_pos (ChartScales.epsilon_pos F.data.h n) _).le,
    normalizedBase_smooth H v upper B U, ?_⟩
  intro m
  obtain ⟨C, hC, hb⟩ := normalizedBase_prefix H v upper B U alpha m
  refine ⟨C + 1, by linarith, 0, fun n p hp j hj => ?_⟩
  simpa only [pow_zero, mul_one] using (hb n p hp j hj).trans
    (mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1)
      (Real.rpow_pos_of_pos (ChartScales.epsilon_pos F.data.h n) alpha).le)

theorem baseError_zero_angle (n : ℕ) (x : BaseContextAssembly.Point) (i : Fin 3) :
    ActualBaseResidual.baseError H v upper B n (x, 0) i =
      normalizedBase H v upper B n (BaseContextAssembly.slowCoordinates x) i := by
  simp only [ActualBaseResidual.baseError, ActualBaseResidual.errorAtScale, neg_zero,
    ActualBaseResidual.physicalPoint_zero_angle, CylindricalResidual.frame_apply,
    Real.cos_zero, Real.sin_zero, one_mul, zero_mul, sub_zero, zero_add, normalizedBase,
    BaseContextAssembly.physicalPoint, PiLp.smul_apply, smul_eq_mul]
  congr 1
  fin_cases i <;> simp

/-- Every actual base-error component has all powers on the full free
auxiliary lift. No vanishing edge-weight premise is imposed on this term. -/
theorem baseError_component_class (alpha : ℝ) (i : Fin 3) :
    UnweightedClass (BaseContextAssembly.nativeStrip W U) alpha
      (fun n x => ActualBaseResidual.baseError H v upper B n (x, 0) i) := by
  have hh := BaseContextAssembly.envelope_pullback (BaseContextAssembly.nativeStrip W U)
    (normalizedBase_envelope H v upper B U alpha)
    (fun _ => BaseContextAssembly.slowCoordinates_maps W U) (fun _ => rfl)
  have hi := hh.map (AxisymmetricFields.projection i)
  apply WaveInteractionBounds.class_congr hi
  intro n x _
  exact (baseError_zero_angle H v upper B n x i).symm

theorem baseError_angle_component_class (alpha : ℝ) (i : Fin 3) :
    UnweightedClass (HarmonicWaveInteraction.productStrip (BaseContextAssembly.nativeStrip W U))
        alpha
      (fun n x => ActualBaseResidual.baseError H v upper B n x i) := by
  have hh := HarmonicWaveInteraction.class_lift (baseError_component_class H v upper B U alpha i)
  apply WaveInteractionBounds.class_congr hh
  intro n x hx
  exact (ActualBaseResidual.baseError_angle_eq H v upper B n
    (BaseContextAssembly.nativeStrip_radius W U hx) (BaseContextAssembly.nativeStrip_time W U hx)
      x.2 i).symm

end NormalizedBase

section NativeGaussianBounds

open CorrectionInitialization PrimaryCopyBounds PhaseJetBounds LocalizedWaveBounds
open ActualPrimaryBounds

variable {B N0 : ℕ}

/-- The genuine fast derivative of the Gaussian cutoff, multiplied by
the actual attached primary solution. -/
noncomputable def nativeGaussian (l : SignedLabel B N0) (x : Native) :
    HarmonicCalculus.ComplexVector :=
  fderiv ℝ (ActualPrimary.gaussian l.2) x (0, (0, 1)) •
    CurlClassBounds.complexify (ActualPrimary.attachedRawVelocity l.1 l.2 x)

theorem nativeGaussian_jets :
    NativeJets (signDomain (NativeBandExtension.radialDomain ActualPrimary.certificate
      ActualPrimary.modulation (ActualPrimary.choice B N0).prepared)) (nativeWeight (1 / 2))
      (nativeGaussian (B := B) (N0 := N0)) :=
  complex_velocity_native_jets.polynomial_smul (gaussian_polynomial.directional (0, (0, 1)))

theorem nativeGaussian_core (l : SignedLabel B N0) (x : Native)
    (hx : nativeGaussian l x ≠ 0) : x.2 ∈ (ActualPrimary.clockWindow l.2).core := by
  apply ActualPrimary.attachedRawVelocity_core l.1 l.2 x
  intro hz
  exact hx (by simp only [nativeGaussian, hz, map_zero, smul_zero])

theorem nativeGaussian_zero_plateau (l : SignedLabel B N0) {x : Native}
    (hx : |x.2.2 / ((ActualPrimary.phases B N0 0).L l.2) - 1 / 2| < 1 / 5) :
    nativeGaussian l =ᶠ[𝓝 x] fun _ => 0 := by
  have hc : ContinuousAt (fun z : Native => z.2.2 / ((ActualPrimary.phases B N0 0).L l.2)) x :=
    continuousAt_snd.snd.div_const _
  have he : ActualPrimary.gaussian l.2 =ᶠ[𝓝 x] fun _ => 1 := by
    exact (GaussianTailFlat.profile_eventually_one hx).comp_tendsto hc.tendsto
  have hd : fderiv ℝ (ActualPrimary.gaussian l.2) =ᶠ[𝓝 x]
      fderiv ℝ (fun _ : Native => (1 : ℝ)) := he.fderiv
  filter_upwards [hd] with z hz
  simp only [nativeGaussian, hz, fderiv_fun_const, Pi.zero_apply, _root_.zero_apply, zero_smul]

/-- Native band scales, bundling `power`, `epsilon_eq`, `boundConstant`, `constant_one_le` and
the required compatibility proofs. -/
noncomputable def nativeBandScales : GaussianTailFlat.BandScaleControl nativeStrip where
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

/-- Gaussian length lower, given by `2 * ActualPrimary.slots.radius / 25`. -/
noncomputable def gaussianLengthLower : ℝ := 2 * ActualPrimary.slots.radius / 25

theorem gaussianLengthLower_pos : 0 < gaussianLengthLower := by
  unfold gaussianLengthLower
  exact div_pos (mul_pos (by norm_num) ActualPrimary.slots.radius_pos) (by norm_num)

theorem gaussianLength_near (l : SignedLabel B N0) (n : ℕ) (hn : near l n) :
    gaussianLengthLower * ChartScales.S n ≤ (ActualPrimary.phases B N0 0).L l.2 := by
  have hs := ActualSignedGeometry.S_window_le
    (show 1 ≤ BaseChartJets.cellBand l.2 by
        have := label_large l; exact Nat.le_trans (by norm_num) this)
    (near_distance hn).1
  have hl := (ChartScales.slotLength_bounds ActualPrimary.slots.radius ActualPrimary.h
    ActualPrimary.slots.radius_pos.le ActualPrimary.outgoing.data.h_pos.le (label_large l)).1
  change 2 * ActualPrimary.slots.radius * ChartScales.S (BaseChartJets.cellBand l.2) ≤
    ChartScales.slotLength ActualPrimary.slots.radius ActualPrimary.h (BaseChartJets.cellBand l.2)
        at hl
  change _ ≤ ChartScales.slotLength ActualPrimary.slots.radius ActualPrimary.h
      (BaseChartJets.cellBand l.2)
  unfold gaussianLengthLower
  nlinarith [mul_le_mul_of_nonneg_left hs ActualPrimary.slots.radius_pos.le]

/-- Outside the active finite band window the copied field is identically
zero. The auxiliary length merely makes the global index bookkeeping total. -/
noncomputable def gaussianLength (l : SignedLabel B N0) (n : ℕ) : ℝ :=
  max ((ActualPrimary.phases B N0 0).L l.2) (gaussianLengthLower * ChartScales.S n)

theorem gaussianLength_pos (l : SignedLabel B N0) (n : ℕ) : 0 < gaussianLength l n :=
  ((ActualPrimary.phases B N0 0).L_pos l.2).trans_le (le_max_left _ _)

theorem gaussianLength_eq (l : SignedLabel B N0) (n : ℕ) (hn : near l n) :
    gaussianLength l n = (ActualPrimary.phases B N0 0).L l.2 :=
  max_eq_left (gaussianLength_near l n hn)

/-- Gaussian rate, given by `ActualGaussianCoverage.gaussianRate (ActualPrimary.choice B
N0).prepared.M⁻¹ (ActualPrimary.choice B N0).prepared.u`. -/
noncomputable def gaussianRate (B N0 : ℕ) : ℝ :=
  ActualGaussianCoverage.gaussianRate (ActualPrimary.choice B N0).prepared.M⁻¹
    (ActualPrimary.choice B N0).prepared.u

theorem gaussianRate_pos (B N0 : ℕ) : 0 < gaussianRate B N0 :=
  ActualGaussianCoverage.prepared_gaussian_rate_pos ActualPrimary.certificate
    ActualPrimary.modulation (ActualPrimary.choice B N0).prepared

theorem nativeEnvelope_gaussian (l : SignedLabel B N0) {v : ℝ}
    (hv : v ∈ Icc 0 ((ActualPrimary.phases B N0 0).L l.2)) :
    pulseEnvelope l v ≤ Real.exp (-gaussianRate B N0 *
      (v / ((ActualPrimary.phases B N0 0).L l.2) - 1 / 2) ^ 2 *
        ((ActualPrimary.phases B N0 0).L l.2)) := by
  have hl := ActualGaussianCoverage.prepared_lambda_lower ActualPrimary.certificate
    ActualPrimary.modulation (ActualPrimary.choice B N0).prepared
    ActualPrimary.slots.radius_pos l.1 l.2
  have hrate := ActualGaussianCoverage.gaussianRate_mono
    (ActualPrimary.choice B N0).prepared.u_pos hl
  have hb := ActualGaussianCoverage.referenceP_scaled_bound
    ((ActualPrimary.phases B N0 l.1).lam_pos l.2)
    ((ActualPrimary.phases B N0 l.1).u_pos l.2)
    ((ActualPrimary.phases B N0 l.1).L_pos l.2) (by norm_num : (0 : ℝ) < 1)
    (show v ∈ Icc 0 (((ActualPrimary.phases B N0 l.1).L l.2) / 1) by
      simpa only [div_one, ActualPrimary.length_sign l.1 l.2] using hv)
  simp only [one_mul, div_one, mul_one, ActualPrimary.length_sign l.1 l.2] at hb
  exact hb.trans (Real.exp_le_exp.mpr (by
    have hL := ((ActualPrimary.phases B N0 0).L_pos l.2).le
    change ActualGaussianCoverage.gaussianRate (ActualPrimary.choice B N0).prepared.M⁻¹
      (ActualPrimary.choice B N0).prepared.u ≤
      ActualGaussianCoverage.gaussianRate ((ActualPrimary.phases B N0 l.1).lam l.2)
        ((ActualPrimary.phases B N0 l.1).u l.2) at hrate
    unfold gaussianRate
    nlinarith [mul_le_mul_of_nonneg_right hrate
      (mul_nonneg (sq_nonneg (v / ((ActualPrimary.phases B N0 0).L l.2) - 1 / 2)) hL)]))

/-- Uniform Gaussian gain before restoring the angular carrier. The
moving edge factor remains `sqrt(zeta)` at every requested exponent. -/
theorem copiedGaussian_all_gains (a β : ℝ) :
    PeriodizedWaveBounds.UniformLocalJets nativeStrip
      (fun _ _ x => Real.sqrt (nativeStrip.zeta x)) β
      (fun l : SignedLabel B N0 => (copyCells l).carrier)
      (copied a nativeGaussian) := by
  let K : ℕ → SignedLabel B N0 × TorusInverse.Frequency → Set Native :=
    fun n i => {x | near i.1 n ∧ x ∈ (copyCells i.1).carrier n i.2}
  have hj := copied_uniformLocalJets (a := a) (nativeGaussian_jets (B := B) (N0 := N0))
  have hlocal : LocalWave nativeStrip K (fun n i x => envelope i.1 n x) (1 / 2)
      (fun n i => copied a nativeGaussian i.1 n i.2) := by
    refine ⟨fun n i x _ => mul_nonneg (Real.sqrt_nonneg _) (envelope_nonneg i.1 n x),
      fun n i x hx hi => hj.smooth i.1 n i.2 x hx hi.2, ?_⟩
    intro m
    obtain ⟨C, hC, p, hb⟩ := hj.bounds m
    exact ⟨C, hC, p, fun n i x hx hi j hj => hb i.1 n i.2 x hx hi.2 j hj⟩
  have hflat := ActualGaussianCoverage.indexed_gaussian_weighted_all_gains hlocal nativeBandScales
    (fun n i x => (copyPoint i.1 n i.2 x).2.2 / ((ActualPrimary.phases B N0 0).L i.1.2))
    (fun n i => gaussianLength i.1 n) (fun n i => gaussianLength_pos i.1 n)
    gaussianLengthLower gaussianLengthLower_pos (fun _ _ => le_max_right _ _)
    (gaussianRate_pos B N0)
    (fun n i x _ hi => by
      rw [gaussianLength_eq i.1 n hi.1, envelope_copy i.1 n i.2 hi.2]
      exact nativeEnvelope_gaussian i.1 hi.2.2)
    (fun n i x _ _ hm => by
      have hz := (nativeGaussian_zero_plateau i.1 hm).comp_tendsto
        (copyPoint_smooth i.1 n i.2).continuous.continuousAt.tendsto
      filter_upwards [hz] with y hy
      change nativeGaussian i.1 (copyPoint i.1 n i.2 y) = 0 at hy
      simp only [copied, hy, smul_zero, ite_self]) β
  have hlarge : LocalClass nativeStrip
      (fun n (i : SignedLabel B N0 × TorusInverse.Frequency) => (copyCells i.1).carrier n i.2)
      (fun _ _ x => Real.sqrt (nativeStrip.zeta x)) β
      (fun n i => copied a nativeGaussian i.1 n i.2) := by
    apply hflat.enlarge
    intro n i x _ hi
    by_cases hn : near i.1 n
    · exact Or.inl ⟨hn, hi⟩
    · exact Or.inr (Filter.Eventually.of_forall (fun _ => ite_eq_right hn))
  exact hlarge.to_uniformLocalJets

theorem periodizedGaussian_all_gains (a β : ℝ) :
    LabelSumBounds.UniformClass nativeStrip (fun _ _ x => Real.sqrt (nativeStrip.zeta x)) β
      (periodized a (nativeGaussian (B := B) (N0 := N0))) := by
  apply PeriodizedWaveBounds.copySum_uniformClass copyCells
    (fun _ _ _ _ => Real.sqrt_nonneg _)
  · intro l n k x hx
    by_cases hn : near l n
    · have hf : nativeGaussian l (copyPoint l n k x) ≠ 0 := by
        intro hz
        exact hx (by simp only [copied, ite_eq_left hn, hz, smul_zero])
      exact nativeGaussian_core l _ hf
    · exact (hx (by simp only [copied, ite_eq_right hn])).elim
  · exact copiedGaussian_all_gains a β

end NativeGaussianBounds

section InitialLabelSupport

open CorrectionInitialization ActualPrimaryBounds

variable {B N0 : ℕ}

/-- The original label's actual slow mask and Gaussian source rectangle,
on the common torus lift. The harmonic index does not change this set. -/
noncomputable def labelCarrier (l : SignedLabel B N0) (n : ℕ) : Set Point :=
  {x | ∃ k : TorusInverse.Frequency,
    (ActualPrimary.nativeSlow l.2 (ActualPrimary.toAbsolute n x),
      (ActualPrimary.geometry l.1 l.2).coordinates k (ActualPrimary.toAbsolute n x).2) ∈
      ActualGaussianCoverage.actualSourceCore ActualPrimary.certificate ActualPrimary.modulation
        (ActualPrimary.choice B N0).prepared l.2}

theorem labelCarrier_closed (l : SignedLabel B N0) (n : ℕ) : IsClosed (labelCarrier l n) := by
  let q : Point → Native := fun x =>
    (ActualPrimary.nativeSlow l.2 (ActualPrimary.toAbsolute n x), (ActualPrimary.toAbsolute n x).2)
  have hq : Continuous q :=
    (((ActualPrimary.nativeSlow_smooth l.2).comp (ActualPrimary.toAbsolute_smooth
        n)).continuous).prodMk
      (ActualPrimary.toAbsolute_smooth n).continuous.snd
  have he : labelCarrier l n = q ⁻¹' ActualGaussianCoverage.sourceRegion
      (ActualGaussianCoverage.actualSlowCore ActualPrimary.certificate ActualPrimary.modulation
        (ActualPrimary.choice B N0).prepared l.2)
      (ActualPrimary.geometry l.1 l.2) ActualPrimary.slots.radius
      (ChartScales.slotLength ActualPrimary.slots.radius ActualPrimary.h (BaseChartJets.cellBand
          l.2)) 1 := by
    ext x
    simp only [labelCarrier, Set.mem_ofPred_eq, mem_preimage, ActualGaussianCoverage.sourceRegion,
      mem_inter_iff, ActualGaussianCoverage.actualSourceCore, mem_prod,
      HarmonicSourceSupport.nativeUnion, mem_iUnion, PeriodizedWaveBounds.nativeCell, q]
    exact exists_and_left
  rw [he]
  exact (ActualGaussianCoverage.sourceRegion_closed
    (ActualGaussianCoverage.actualSlowCore_closed ActualPrimary.certificate ActualPrimary.modulation
      (ActualPrimary.choice B N0).prepared l.2) _ _ _ _).preimage hq

theorem nativeGaussian_source_support (l : SignedLabel B N0) :
    support (nativeGaussian l) ⊆
      ActualGaussianCoverage.actualSourceCore ActualPrimary.certificate ActualPrimary.modulation
        (ActualPrimary.choice B N0).prepared l.2 := by
  intro x hx
  have ha : ActualPrimary.attachedRawVelocity l.1 l.2 x ≠ 0 := by
    intro hz
    exact hx (by simp only [nativeGaussian, hz, map_zero, smul_zero])
  have ho : ActualPrimary.outerRawVelocity l.1 l.2 x ≠ 0 := by
    intro hz
    exact ha (by simp [ActualPrimary.attachedRawVelocity, WaveEdgeExtension.nativeExtension,
      WaveEdgeExtension.extension, hz])
  have hr : ActualPrimary.rawVelocity l.1 l.2 x ≠ 0 := by
    intro hz
    exact ho (by simp only [ActualPrimary.outerRawVelocity, hz, smul_zero])
  have hm : ActualPrimary.spatialMask l.2 x.1 ≠ 0 := by
    intro hz
    exact hr (by simp [ActualPrimary.rawVelocity, PartitionedCovariance.amplitude, hz])
  have hs := ActualPrimary.spatialMask_native_support l.2 x.1 hm
  have ht := ActualPrimary.rawVelocity_transverse l.1 l.2 x hr
  have hg : |x.2.2 / ((ActualPrimary.phases B N0 0).L l.2) - 1 / 2| ≤ 1 / 3 := by
    by_contra hn
    have he : ActualPrimary.gaussian l.2 =ᶠ[𝓝 x] fun _ => 0 :=
      (GaussianTailFlat.profile_eventually_zero (lt_of_not_ge hn)).comp_tendsto
        (continuous_snd.snd.div_const _).continuousAt.tendsto
    exact hx (by simp only [nativeGaussian, he.fderiv_eq, fderiv_fun_const,
      Pi.zero_apply, _root_.zero_apply, zero_smul])
  have hL := (ActualPrimary.phases B N0 0).L_pos l.2
  have hlo : (1 / 6 : ℝ) ≤ x.2.2 / ((ActualPrimary.phases B N0 0).L l.2) := by
    linarith [(abs_le.mp hg).1]
  have hhi : x.2.2 / ((ActualPrimary.phases B N0 0).L l.2) ≤ 5 / 6 := by
    linarith [(abs_le.mp hg).2]
  refine ⟨hs, ⟨ht.1.le, ht.2.le⟩, ?_, ?_⟩
  · change ((ActualPrimary.phases B N0 0).L l.2 / 1) / 6 ≤ x.2.2
    simpa only [div_eq_mul_inv, inv_one, mul_one, one_mul, mul_comm] using
      (le_div_iff₀ hL).mp hlo
  · change x.2.2 ≤ 5 * ((ActualPrimary.phases B N0 0).L l.2 / 1) / 6
    simpa only [div_eq_mul_inv, inv_one, mul_one, one_mul, mul_comm, mul_assoc, mul_left_comm] using
      (div_le_iff₀ hL).mp hhi

theorem nativeGaussian_source_tsupport (l : SignedLabel B N0) :
    tsupport (nativeGaussian l) ⊆
      ActualGaussianCoverage.actualSourceCore ActualPrimary.certificate ActualPrimary.modulation
        (ActualPrimary.choice B N0).prepared l.2 :=
  closure_minimal (nativeGaussian_source_support l)
    (ActualGaussianCoverage.actualSourceCore_closed ActualPrimary.certificate
        ActualPrimary.modulation
      (ActualPrimary.choice B N0).prepared l.2)

end InitialLabelSupport

section ActualGaussianIdentification

open CorrectionInitialization ActualPrimaryBounds

variable {B N0 : ℕ}

/-- Chart gaussian, constructed using `LinearWaveBounds.excludedSlotError`. -/
noncomputable def chartGaussian (l : SignedLabel B N0) :
    ℕ → ActualPrimary.FullPoint → HarmonicCalculus.ComplexVector :=
  LinearWaveBounds.excludedSlotError (PrimaryResidualClass.directions (ActualPrimary.commonContext
      B))
    (ActualPrimary.chartCutoff l.1 l.2) (ActualPrimary.chartCoefficients l.1 l.2).amplitude 0

theorem nativeGaussian_smooth (L : ActualPrimary.Label B N0) :
    ContDiff ℝ ∞ (ActualPrimary.gaussian L) :=
  GaussianTailFlat.profile_contDiff.comp (contDiff_snd.snd.div_const _)

theorem chartCutoff_germ (l : SignedLabel B N0) (n : ℕ) (k : TorusInverse.Frequency)
    {x : ActualPrimary.FullPoint}
    (hc : (ActualPrimaryDynamics.copyPoint l.1 l.2 n k x).2 ∈ (ActualPrimary.clockWindow l.2).core)
        :
    ActualPrimary.chartCutoff l.1 l.2 n =ᶠ[𝓝 x]
      fun y => ActualPrimary.gaussian l.2 (ActualPrimaryDynamics.copyPoint l.1 l.2 n k y) := by
  have he := PeriodicPhaseAssembly.periodicClock_germ (ActualPrimary.geometry l.1 l.2)
    (ActualPrimary.clockWindow l.2) (ActualPrimary.clockWindow_injective l.1 l.2) k
    (z := ActualPrimaryDynamics.coefficientPoint l.2 n x) hc
  filter_upwards [(ActualPrimaryDynamics.coefficientPoint_smooth l.2
      n).continuous.continuousAt.eventually he]
    with y hy
  dsimp only [ActualPrimaryDynamics.coefficientPoint] at hy
  change GaussianTailFlat.profile (_ / _) = GaussianTailFlat.profile (_ / _)
  rw [hy]
  rfl

theorem fast_nativeGaussian (l : SignedLabel B N0) (n : ℕ) (k : TorusInverse.Frequency)
    (x : ActualPrimary.FullPoint) :
    fderiv ℝ (fun y => ActualPrimary.gaussian l.2 (ActualPrimaryDynamics.copyPoint l.1 l.2 n k y)) x
      ((PrimaryResidualClass.directions (ActualPrimary.commonContext B)).fastField n x) =
        ActualPrimaryDynamics.clockScale l.2 n *
          fderiv ℝ (ActualPrimary.gaussian l.2) (ActualPrimaryDynamics.copyPoint l.1 l.2 n k x) (0,
              (0, 1)) := by
  change fderiv ℝ (ActualPrimary.gaussian l.2 ∘ ActualPrimaryDynamics.copyPoint l.1 l.2 n k) x _ = _
  rw [fderiv_comp x ((nativeGaussian_smooth l.2).differentiable (by simp)).differentiableAt
    (ActualPrimaryDynamics.copyPoint_hasFDerivAt l.1 l.2 n k x).differentiableAt,
    ContinuousLinearMap.comp_apply, (ActualPrimaryDynamics.copyPoint_hasFDerivAt l.1 l.2 n k
        x).fderiv,
    ActualPrimaryDynamics.copyLinear_fast]
  have he : (0, (0, ActualPrimaryDynamics.clockScale l.2 n)) =
      ActualPrimaryDynamics.clockScale l.2 n • ((0, (0, 1)) : Native) := by ext <;> simp
  rw [he, map_smul, smul_eq_mul]

theorem gaussianScale_eq (l : SignedLabel B N0) (n : ℕ) :
    ActualPrimaryDynamics.clockScale l.2 n * ActualPrimaryDynamics.velocityScale l.2 n =
      coefficientScale (2 * CoordinateAlgebra.A ActualPrimary.h + 1 / 2) l n := by
  unfold ActualPrimaryDynamics.clockScale ActualPrimaryDynamics.velocityScale
    coefficientScale PhysicalParticularWave.ratioPower
  rw [div_mul_div_comm, ← Real.rpow_add (ChartScales.Q_pos n),
    ← Real.rpow_add (ChartScales.Q_pos (BaseChartJets.cellBand l.2))]
  have he : 1 + ActualPrimary.h + CoordinateAlgebra.A ActualPrimary.h =
      2 * CoordinateAlgebra.A ActualPrimary.h + 1 / 2 := by unfold CoordinateAlgebra.A; ring
  rw [he]

theorem chartGaussian_germ (l : SignedLabel B N0) (n : ℕ) (k : TorusInverse.Frequency)
    {x : ActualPrimary.FullPoint}
    (hc : (ActualPrimaryDynamics.copyPoint l.1 l.2 n k x).2 ∈ (ActualPrimary.clockWindow l.2).core)
        :
    chartGaussian l n =ᶠ[𝓝 x] fun y =>
      coefficientScale (2 * CoordinateAlgebra.A ActualPrimary.h + 1 / 2) l n •
        nativeGaussian l (ActualPrimaryDynamics.copyPoint l.1 l.2 n k y) := by
  have hd : fderiv ℝ (ActualPrimary.chartCutoff l.1 l.2 n) =ᶠ[𝓝 x]
      fderiv ℝ (fun y => ActualPrimary.gaussian l.2 (ActualPrimaryDynamics.copyPoint l.1 l.2 n k
          y)) :=
    (chartCutoff_germ l n k hc).fderiv
  filter_upwards [hd, ActualPrimaryDynamics.amplitude_germ l.1 l.2 n k hc] with y hy ha
  simp only [chartGaussian, LinearWaveBounds.excludedSlotError,
      LinearWaveBounds.GraphDirections.Dfast,
    LinearWaveBounds.GraphDirections.fastField, HarmonicCalculus.along, Pi.zero_apply, smul_zero,
    add_zero, hy, ha]
  change fderiv ℝ (fun y => ActualPrimary.gaussian l.2 (ActualPrimaryDynamics.copyPoint l.1 l.2 n k
      y)) y
    ((PrimaryResidualClass.directions (ActualPrimary.commonContext B)).fastField n y) •
      (ActualPrimaryDynamics.velocityScale l.2 n • _) = _
  rw [fast_nativeGaussian]
  simp only [nativeGaussian, smul_smul]
  rw [mul_right_comm, gaussianScale_eq]

theorem chartGaussian_zero_no_copy (l : SignedLabel B N0) (n : ℕ) {x : ActualPrimary.FullPoint}
    (hc : ∀ k : TorusInverse.Frequency,
      (ActualPrimaryDynamics.copyPoint l.1 l.2 n k x).2 ∉ (ActualPrimary.clockWindow l.2).core) :
    chartGaussian l n =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [(ActualPrimaryDynamics.coefficient_zero_germs l.1 l.2 n hc).1] with y hy
  simp only [chartGaussian, LinearWaveBounds.excludedSlotError, hy, Pi.zero_apply, smul_zero,
      add_zero]

theorem chartGaussian_support (l : SignedLabel B N0) (n : ℕ) :
    support (chartGaussian l n) ⊆ Prod.fst ⁻¹' labelCarrier l n := by
  intro x hx
  by_contra hn
  by_cases hc : ∃ k : TorusInverse.Frequency,
      (ActualPrimaryDynamics.copyPoint l.1 l.2 n k x).2 ∈ (ActualPrimary.clockWindow l.2).core
  · obtain ⟨k, hk⟩ := hc
    have hg := (chartGaussian_germ l n k hk).eq_of_nhds
    have hz : nativeGaussian l (ActualPrimaryDynamics.copyPoint l.1 l.2 n k x) = 0 := by
      by_contra hz
      exact hn ⟨k, nativeGaussian_source_support l hz⟩
    exact hx (by rw [hg, hz, smul_zero])
  · exact hx (chartGaussian_zero_no_copy l n (not_exists.mp hc)).eq_of_nhds

theorem chartGaussian_zero_germ (l : SignedLabel B N0) (n : ℕ) {x : ActualPrimary.FullPoint}
    (hx : x.1 ∉ labelCarrier l n) : chartGaussian l n =ᶠ[𝓝 x] fun _ => 0 :=
  notMem_tsupport_iff_eventuallyEq.mp (fun hz => hx
    (closure_minimal (chartGaussian_support l n) ((labelCarrier_closed l n).preimage
        continuous_fst) hz))

theorem dynamics_copyPoint_eq (l : SignedLabel B N0) (n : ℕ) (hn : near l n)
    (k : TorusInverse.Frequency) (x : Native) (θ : ℝ) :
    ActualPrimaryDynamics.copyPoint l.1 l.2 n k (ActualSignedGeometry.meanEquiv x, θ) =
      copyPoint l n k x := by
  have he := ActualPrimary.chart_nativePoint l.1 l.2 n (CommonWindow.index_le hn.2) k
    (ActualSignedGeometry.meanEquiv x)
  simp only [ActualSignedGeometry.meanEquiv.symm_apply_apply] at he
  exact he

theorem periodizedGaussian_eq (l : SignedLabel B N0) (n : ℕ) {x : Native}
    (hx : x ∈ nativeStrip.domain) (θ : ℝ) :
    periodized (2 * CoordinateAlgebra.A ActualPrimary.h + 1 / 2) nativeGaussian l n x =
      chartGaussian l n (ActualSignedGeometry.meanEquiv x, θ) := by
  classical
  let a := 2 * CoordinateAlgebra.A ActualPrimary.h + 1 / 2
  have hs (k : TorusInverse.Frequency) : support (copied a nativeGaussian l n k) ⊆
      (copyCells l).carrier n k := by
    intro y hy
    by_cases hn : near l n
    · have hg : nativeGaussian l (copyPoint l n k y) ≠ 0 := by
        intro hz
        exact hy (by simp only [copied, ite_eq_left hn, hz, smul_zero])
      exact nativeGaussian_core l _ hg
    · exact (hy (by simp only [copied, ite_eq_right hn])).elim
  by_cases hn : near l n
  · by_cases hc : ∃ k, x ∈ (copyCells l).carrier n k
    · obtain ⟨k, hk⟩ := hc
      have hpoint := dynamics_copyPoint_eq l n hn k x θ
      have hactual : (ActualPrimaryDynamics.copyPoint l.1 l.2 n k
          (ActualSignedGeometry.meanEquiv x, θ)).2 ∈ (ActualPrimary.clockWindow l.2).core := by
        rw [hpoint]
        exact hk
      rw [(chartGaussian_germ l n k hactual).eq_of_nhds, hpoint]
      exact (PeriodizedWaveBounds.copySum_germ (copyCells l) n
        (copied a nativeGaussian l n) hs hk).eq_of_nhds.trans (ite_eq_left hn)
    · have hactual : ∀ k, (ActualPrimaryDynamics.copyPoint l.1 l.2 n k
          (ActualSignedGeometry.meanEquiv x, θ)).2 ∉ (ActualPrimary.clockWindow l.2).core := by
        intro k hk
        rw [dynamics_copyPoint_eq l n hn k x θ] at hk
        exact hc ⟨k, hk⟩
      rw [(chartGaussian_zero_no_copy l n hactual).eq_of_nhds]
      exact (PeriodizedWaveBounds.copySum_zero_germ (copyCells l) n
        (copied a nativeGaussian l n) hs (not_exists.mp hc)).eq_of_nhds
  · have hzero : (ActualPrimary.chartCoefficients l.1 l.2).amplitude n
        (ActualSignedGeometry.meanEquiv x, θ) = 0 := by
      rw [← periodized_velocity_eq l n hx θ]
      simp only [periodized, PeriodizedWaveBounds.copySum, copied, ite_eq_right hn, tsum_zero]
    simp only [periodized, PeriodizedWaveBounds.copySum, copied, ite_eq_right hn, tsum_zero,
      chartGaussian, LinearWaveBounds.excludedSlotError, hzero, Pi.zero_apply, smul_zero, add_zero]

/-- The actual initialized Gaussian coefficient, uniformly in every
label and on the entire free auxiliary and angular lift. -/
theorem chartGaussian_all_gains (β : ℝ) :
    LabelSumBounds.UniformClass (HarmonicWaveInteraction.productStrip strip)
      (fun _ _ x => Real.sqrt (strip.zeta x.1)) β (chartGaussian (B := B) (N0 := N0)) := by
  have hh := UniformBlockBounds.uniform_reindex ActualSignedGeometry.meanEquiv.symm
    (periodizedGaussian_all_gains (B := B) (N0 := N0)
      (2 * CoordinateAlgebra.A ActualPrimary.h + 1 / 2) β)
  change LabelSumBounds.UniformClass strip (fun _ _ x => Real.sqrt (strip.zeta x)) β
    (fun l n x => periodized (2 * CoordinateAlgebra.A ActualPrimary.h + 1 / 2)
      nativeGaussian l n (ActualSignedGeometry.meanEquiv.symm x)) at hh
  apply (uniform_lift hh).congr
  intro l n x hx
  simpa only [ActualSignedGeometry.meanEquiv.apply_symm_apply] using
    periodizedGaussian_eq l n (x := ActualSignedGeometry.meanEquiv.symm x.1) hx x.2

theorem gaussianCoefficient_all_gains (β : ℝ) (i : Fin 3) (j : ℤ) :
    LabelSumBounds.UniformClass strip (fun _ _ x => Real.sqrt (strip.zeta x)) β
      (fun l : SignedLabel B N0 => fun n x => ErrorHarmonics.conjugatePair 1
        (fun y => chartGaussian l n (y, 0) i) j x) := by
  have hs : LabelSumBounds.UniformClass strip
      (fun _ : SignedLabel B N0 => fun _ x => Real.sqrt (strip.zeta x)) β
      (fun l n x => chartGaussian l n (x, 0)) :=
    UniformBlockBounds.uniform_slice (chartGaussian_all_gains (B := B) (N0 := N0) β)
  have hi : LabelSumBounds.UniformClass strip
      (fun _ : SignedLabel B N0 => fun _ x => Real.sqrt (strip.zeta x)) β
      (fun l n x => chartGaussian l n (x, 0) i) := hs.map (ContinuousLinearMap.proj i)
  exact UniformBlockBounds.pair_uniform hi 1 j

theorem gaussianCoefficient_zero (l : SignedLabel B N0) (n : ℕ) (i : Fin 3) (j : ℤ)
    {x : Point} (hx : x ∉ labelCarrier l n) :
    ErrorHarmonics.conjugatePair 1 (fun y => chartGaussian l n (y, 0) i) j x = 0 := by
  have hz : chartGaussian l n (x, 0) = 0 := (chartGaussian_zero_germ l n hx).eq_of_nhds
  simp only [ParticularWaveAssembly.pair_apply, hz, Pi.zero_apply, zero_div]
  split_ifs <;> simp

theorem gaussianCoefficient_support (l : SignedLabel B N0) (n : ℕ) (i : Fin 3) :
    HarmonicSourceSupport.NonzeroSupported (labelCarrier l n)
      (ErrorHarmonics.conjugatePair 1 (fun y => chartGaussian l n (y, 0) i)) := by
  intro j _ x hx
  exact gaussianCoefficient_zero l n i j hx

end ActualGaussianIdentification

section FlatProducts

variable {D : Type} {I : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {s : StripData D} {w : I → ℕ → D → ℝ} {K : I → ℕ → Set D}
  {f g : I → ℕ → D → ℂ}

/-- Only carrier jets on the actual coefficient support are used. Their
fixed-order loss is absorbed by the independently proved all-power input. -/
theorem uniform_flat_mul
    (hf : ∀ α : ℝ, LabelSumBounds.UniformClass s w α f)
    (hg : ∀ i n, ContDiffOn ℝ ∞ (g i n) s.domain)
    (hz : ∀ i n x, x ∈ s.domain → x ∉ K i n → f i n =ᶠ[𝓝 x] fun _ => 0)
    (hb : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∃ r : ℝ,
      ∀ i n x, x ∈ s.domain → x ∈ K i n → ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (g i n) x‖ ≤ majorant s (fun _ _ => 1) r C p n x)
    (β : ℝ) : LabelSumBounds.UniformClass s w β (fun i n x => f i n x * g i n x) := by
  refine ⟨(hf β).weight_nonneg, fun i n => ((hf β).smooth i n).mul (hg i n), ?_⟩
  intro m
  obtain ⟨B, hB, q, r, hgb⟩ := hb m
  obtain ⟨A, hA, p, hfb⟩ := (hf (β-r)).bounds m
  let c := ‖ContinuousLinearMap.mul ℝ ℂ‖ * (2 : ℝ)^m * A * B
  refine ⟨c, by dsimp [c]; positivity, p+q, ?_⟩
  intro i n x hx j hj
  by_cases hK : x ∈ K i n
  · have h := LabelSumBounds.bilinear_jet_bound (ContinuousLinearMap.mul ℝ ℂ)
      s.isOpen_domain ((hf (β-r)).smooth i n) (hg i n) hx hj
      (majorant_nonneg s (w i) (β-r) hA p n x ((hf (β-r)).weight_nonneg i n x hx))
      (majorant_nonneg s (fun _ _ => 1) r hB q n x zero_le_one)
      (hfb i n x hx) (hgb i n x hx hK)
    refine h.trans_eq ?_
    calc
      _ = (‖ContinuousLinearMap.mul ℝ ℂ‖ * (2 : ℝ)^m) *
          (majorant s (w i) (β-r) A p n x * majorant s (fun _ _ => 1) r B q n x) := by ring
      _ = _ := by
        rw [majorant_mul]
        simp only [mul_one, sub_add_cancel]
        unfold majorant c
        ring
  · have he : (fun y => f i n y * g i n y) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hz i n x hx hK] with y hy
      rw [hy, zero_mul]
    rw [PeriodizedWaveBounds.jets_eq_of_germ he j]
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] using
      majorant_nonneg s (w i) β (by dsimp [c]; positivity) (p+q) n x
        ((hf β).weight_nonneg i n x hx)

end FlatProducts

section FullGaussian

open CorrectionInitialization ActualPrimaryBounds

variable {B N0 : ℕ}

/-- Gaussian strip: an abbreviation for `HarmonicWaveInteraction.productStrip strip`. -/
noncomputable abbrev gaussianStrip : StripData ActualPrimary.FullPoint :=
  HarmonicWaveInteraction.productStrip strip

/-- Chart carrier, constructed using `HarmonicCalculus.carrier`. -/
noncomputable def chartCarrier (l : SignedLabel B N0) (n : ℕ) : ActualPrimary.FullPoint → ℂ :=
  HarmonicCalculus.carrier ((ActualPrimary.chartCoefficients l.1 l.2).frequency n)
    ((ActualPrimary.chartCoefficients l.1 l.2).phase n)

theorem chartCarrier_smooth (l : SignedLabel B N0) (n : ℕ) :
    ContDiffOn ℝ ∞ (chartCarrier l n) gaussianStrip.domain :=
  HarmonicCalculus.contDiffOn_carrier ((ActualPrimary.chartCoefficients l.1 l.2).frequency n)
    (ActualPrimaryCoherence.piece_phase_smooth ActualPrimary.standardRegion l.1 l.2 n)

/-- Gaussian field, given by `(ActualPrimary.piece ActualPrimary.standardRegion l.1
l.2).excluded`. -/
noncomputable def gaussianField (l : SignedLabel B N0) :
    ℕ → ActualPrimary.FullPoint → Fin 3 → ℝ :=
  (ActualPrimary.piece ActualPrimary.standardRegion l.1 l.2).excluded

theorem gaussianField_eq (l : SignedLabel B N0) (n : ℕ) (x : ActualPrimary.FullPoint) (i : Fin 3) :
    gaussianField l n x i = (chartGaussian l n x i * HarmonicCalculus.carrier
      ((ActualPrimary.chartCoefficients l.1 l.2).frequency n)
      ((ActualPrimary.chartCoefficients l.1 l.2).phase n) x).re := rfl

theorem chartGaussian_cut_support (l : SignedLabel B N0) (n : ℕ) {x : ActualPrimary.FullPoint}
    (hx : chartGaussian l n x ≠ 0) :
    x ∈ support (((ActualPrimary.chartCoefficients l.1 l.2).withCutoff
      (ActualPrimary.chartCutoff l.1 l.2)).amplitude n) := by
  have ha : (ActualPrimary.chartCoefficients l.1 l.2).amplitude n x ≠ 0 := by
    intro hz
    exact hx (by simp only [chartGaussian, LinearWaveBounds.excludedSlotError,
      hz, Pi.zero_apply, smul_zero, add_zero])
  have hψ : ActualPrimary.chartCutoff l.1 l.2 n x ≠ 0 := by
    intro hz
    have hmin : IsLocalMin (ActualPrimary.chartCutoff l.1 l.2 n) x := by
      apply Filter.Eventually.of_forall
      intro y
      rw [hz]
      exact (GaussianTailFlat.profile_mem_Icc _).1
    exact hx (by simp only [chartGaussian, LinearWaveBounds.excludedSlotError,
      LinearWaveBounds.GraphDirections.Dfast, HarmonicCalculus.along, hmin.fderiv_eq_zero,
      _root_.zero_apply, Pi.zero_apply, zero_smul, smul_zero, add_zero])
  exact smul_ne_zero hψ ha

theorem chartGaussian_zero_off_cut (l : SignedLabel B N0) (n : ℕ) {x : ActualPrimary.FullPoint}
    (hx : x ∉ tsupport (((ActualPrimary.chartCoefficients l.1 l.2).withCutoff
      (ActualPrimary.chartCutoff l.1 l.2)).amplitude n)) :
    chartGaussian l n =ᶠ[𝓝 x] fun _ => 0 := by
  apply notMem_tsupport_iff_eventuallyEq.mp
  exact fun hz => hx (closure_mono (fun y hy => chartGaussian_cut_support l n hy) hz)

theorem gaussianField_window (l : SignedLabel B N0) (n : ℕ) {x : ActualPrimary.FullPoint}
    (hx : x ∈ gaussianStrip.domain) (i : Fin 3) (hn : gaussianField l n x i ≠ 0) :
    ActualPrimaryCovariance.physicalWindow n x.1 ∈
      LabelSumBounds.closedWindow (CoordinateAlgebra.D ActualPrimary.h)
        (ActualPrimaryCovariance.signedLabelOf (l.2,l.1)) := by
  have hc : chartGaussian l n x ≠ 0 := by
    intro hz
    exact hn (by simp only [gaussianField_eq, hz, Pi.zero_apply, zero_mul, Complex.zero_re])
  exact (ActualPrimaryCovariance.piece_support (l.2,l.1) n x.1 hx x.2
    (subset_tsupport _ (chartGaussian_cut_support l n hc))).1

theorem gaussianField_zero_germ (l : SignedLabel B N0) (n : ℕ) (i : Fin 3)
    {x : ActualPrimary.FullPoint} (hx : x.1 ∉ labelCarrier l n) :
    (fun y => gaussianField l n y i) =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [chartGaussian_zero_germ l n hx] with y hy
  simp only [gaussianField_eq, hy, Pi.zero_apply, zero_mul, Complex.zero_re]

theorem gaussianField_all_gains_of_carrier
    (hc : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∃ r : ℝ,
      ∀ (l : SignedLabel B N0) n x, x ∈ gaussianStrip.domain →
        x ∈ tsupport (((ActualPrimary.chartCoefficients l.1 l.2).withCutoff
          (ActualPrimary.chartCutoff l.1 l.2)).amplitude n) → ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (HarmonicCalculus.carrier
          ((ActualPrimary.chartCoefficients l.1 l.2).frequency n)
          ((ActualPrimary.chartCoefficients l.1 l.2).phase n)) x‖ ≤
            majorant gaussianStrip (fun _ _ => 1) r C p n x)
    (β : ℝ) (i : Fin 3) :
    LabelSumBounds.UniformClass gaussianStrip (fun _ _ x => Real.sqrt (strip.zeta x.1)) β
      (fun l : SignedLabel B N0 => fun n x => gaussianField l n x i) := by
  have hf : LabelSumBounds.UniformClass gaussianStrip
      (fun _ : SignedLabel B N0 => fun _ x => Real.sqrt (strip.zeta x.1)) β
      (fun l n x => chartGaussian l n x i * chartCarrier l n x) :=
    uniform_flat_mul (s := gaussianStrip)
    (f := fun (l : SignedLabel B N0) n x => chartGaussian l n x i)
    (g := chartCarrier (B := B) (N0 := N0))
    (fun α => (chartGaussian_all_gains (B := B) (N0 := N0) α).map (ContinuousLinearMap.proj i))
    (chartCarrier_smooth (B := B) (N0 := N0))
    (K := fun (l : SignedLabel B N0) n => tsupport (((ActualPrimary.chartCoefficients l.1
        l.2).withCutoff
      (ActualPrimary.chartCutoff l.1 l.2)).amplitude n))
    (fun l n x _ hx => by
      filter_upwards [chartGaussian_zero_off_cut l n hx] with y hy
      exact congrFun hy i)
    hc β
  apply (hf.map Complex.reCLM).congr
  intro l n x _
  exact (gaussianField_eq l n x i).symm

/-- Initial gaussian, constructed using `LabelSumBounds.fieldSum`. -/
noncomputable def initialGaussian (B N0 : ℕ) : ℕ → ActualPrimary.FullPoint → Fin 3 → ℝ :=
  LabelSumBounds.fieldSum (ActualPrimary.activeLabels ActualPrimary.standardRegion B N0)
    (fun l => (ActualPrimary.piece ActualPrimary.standardRegion l.2 l.1).excluded)

/-- The number of active labels may grow, but at most the fixed geometric
overlap number contributes to an actual derivative at one point. -/
theorem initialGaussian_class_of_fields (β : ℝ) (i : Fin 3)
    (hf : LabelSumBounds.UniformClass gaussianStrip
      (fun _ _ x => Real.sqrt (strip.zeta x.1)) β
      (fun l : SignedLabel B N0 => fun n x => gaussianField l n x i)) :
    MemClass gaussianStrip (fun _ x => Real.sqrt (strip.zeta x.1)) β
      (fun n x => initialGaussian B N0 n x i) := by
  have h := hf.reindex (fun l : ActualPrimary.Label B N0 × Fin 2 => (l.2,l.1))
  have hχ (n : ℕ) : ContinuousOn
      (fun x : ActualPrimary.FullPoint => ActualPrimaryCovariance.physicalWindow n x.1)
      gaussianStrip.domain :=
    (ActualPrimaryCovariance.physicalWindow_continuousOn n).comp
      continuous_fst.continuousOn (fun _ hx => hx)
  exact LabelSumBounds.window_sum_memClass (s := gaussianStrip)
    (w := fun _ x => Real.sqrt (strip.zeta x.1))
    (ActualPrimary.activeLabels ActualPrimary.standardRegion B N0)
    (fun _ => ActualPrimaryCovariance.signedLabelOf)
    (fun _ => ActualPrimaryCovariance.signedLabelOf_injective.injOn)
    (fun _ l _ => l.1.val.property.1)
    (CoordinateAlgebra.D ActualPrimary.h)
    (fun n x => ActualPrimaryCovariance.physicalWindow n x.1)
    hχ h
    (fun _ _ _ => Real.sqrt_nonneg _)
    (fun n l _ x hx hn => gaussianField_window (l.2,l.1) n hx i hn)

theorem strip_zeta_le_one (x : Point) : strip.zeta x ≤ 1 :=
  GaugeExcludedBounds.movingStrip_zeta_le_one ActualPrimary.standardRegion
    (PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal)
    (div_pos (FinalSlowBase.edgeExponent_pos ActualPrimary.nominal) (by norm_num)) zero_lt_one
    (ChartScales.epsilon ActualPrimary.h) BaseContextAssembly.slowScale
    (ChartScales.epsilon_pos ActualPrimary.h)
    (ChartScales.epsilon_le_one ActualPrimary.h ActualPrimary.outgoing.data.h_pos.le)
    BaseContextAssembly.one_le_slowScale x

theorem initialGaussian_unweighted_of_fields (β : ℝ) (i : Fin 3)
    (hf : LabelSumBounds.UniformClass gaussianStrip
      (fun _ _ x => Real.sqrt (strip.zeta x.1)) β
      (fun l : SignedLabel B N0 => fun n x => gaussianField l n x i)) :
    UnweightedClass gaussianStrip β (fun n x => initialGaussian B N0 n x i) :=
  (initialGaussian_class_of_fields β i hf).mono_weight (fun _ _ _ => zero_le_one)
    (fun _ x _ => Real.sqrt_le_one.mpr (strip_zeta_le_one x.1))

end FullGaussian

section InitialAliases

open CorrectionInitialization ActualPrimaryBounds

variable {B N0 : ℕ}

theorem primary_axial_class (d : ActualInitialMean.PrimaryData B N0) :
    MeanClass strip (1 - ChartScales.kappa)
      ((ActualInitialMean.primary B N0).axialResidual (ActualPrimary.commonContext B)) := by
  unfold ActualInitialMean.PrimaryData at d
  have hh := MovingInitialization.zeroMean_reconstructed_bounds
    (cL := FinalSlowBase.edgeExponent ActualPrimary.nominal / 4) (cR := 1)
        ActualPrimary.standardRegion
    ActualPrimary.commonGauge (PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal)
    d.exponent_pos (div_pos (FinalSlowBase.edgeExponent_pos ActualPrimary.nominal) (by
        norm_num)) zero_lt_one
    (ChartScales.epsilon ActualPrimary.h) BaseContextAssembly.slowScale
    (ChartScales.epsilon_pos ActualPrimary.h)
    (ChartScales.epsilon_le_one ActualPrimary.h ActualPrimary.outgoing.data.h_pos.le)
    BaseContextAssembly.one_le_slowScale d.gauge_length (ActualPrimary.commonContext B)
    (ActualInitialMean.seed B N0) d.operators d.localOperators d.mean_zero d.covariance
    d.covariance_smooth d.covariance_support d.theta d.axial
  exact hh.2.2.2.1

theorem temporalAlias_all_gains_of_primaryData (d : ActualInitialMean.PrimaryData B N0) (β : ℝ) :
    MeanClass strip β (fun n x => VariableGaugeMean.temporalAliasState ActualPrimary.commonGauge
      ActualPrimary.h (CommonWindow.index ActualPrimary.h) (ActualPrimary.commonContext B)
      (ActualInitialMean.primary B N0) n (x,0)) ∧
    MeanClass gaussianStrip β (VariableGaugeMean.temporalAliasState ActualPrimary.commonGauge
      ActualPrimary.h (CommonWindow.index ActualPrimary.h) (ActualPrimary.commonContext B)
      (ActualInitialMean.primary B N0)) := by
  have hh := GaugeExcludedBounds.temporalAliasState_mean_bounds ActualPrimary.standardRegion
    (PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal)
    (PrimaryTargetBounds.radii_ordered ActualPrimary.nominal)
    (div_pos (FinalSlowBase.edgeExponent_pos ActualPrimary.nominal) (by norm_num)) zero_lt_one
    ActualPrimary.outgoing.data.h_pos (by norm_num : (1 : ℝ) ≠ 0)
    (CommonWindow.index ActualPrimary.h) (CommonWindow.gap ActualPrimary.h)
    (CommonWindow.native_le_index_add ActualPrimary.h ActualPrimary.outgoing.data.h_pos.le)
    (fun n => (CommonWindow.index_le_native ActualPrimary.h n).trans (Nat.le_add_right _ _))
    BaseContextAssembly.slowScale BaseContextAssembly.one_le_slowScale (fun _ => le_max_right _ _)
    (ActualPrimary.commonContext B) (ActualInitialMean.primary B N0)
    (ActualInitialCoherence.primary_primitive B N0)
    (by dsimp only [GaugeExcludedBounds.actualGauge]
        rw [← ActualInitialCoherence.commonGauge_eq_similarity]; rfl) rfl rfl
    (primary_axial_class d) β
  dsimp only [GaugeExcludedBounds.actualGauge] at hh
  rw [← ActualInitialCoherence.commonGauge_eq_similarity] at hh
  exact hh

theorem pressureAlias_all_gains_of_cumulative (d : ActualInitialMean.PrimaryData B N0)
    (hu : CorrectionState.CumulativeBounds strip (ActualInitialMean.ranked B N0)) (β : ℝ) :
    MeanClass strip β (fun n x => VariableGaugeMean.pressureAliasState ActualPrimary.commonGauge
      (ActualPrimary.commonContext B) (ActualInitialMean.ranked B N0) n (x,0)) ∧
    MeanClass gaussianStrip β (VariableGaugeMean.pressureAliasState ActualPrimary.commonGauge
      (ActualPrimary.commonContext B) (ActualInitialMean.ranked B N0)) := by
  unfold ActualInitialMean.PrimaryData at d
  have hW : ∀ i j, MeanClass strip 1 ((ActualInitialMean.ranked B N0).covariance i j) := by
    intro i j
    simp only [CorrectionState.State.covariance, ActualInitialMean.ranked,
      ActualInitialMean.temporal, ActualInitialMean.primary, VariableGaugeMean.rankStageState,
      VariableGaugeMean.temporalStageState, VariableGaugeMean.reconstructState,
      CorrectionState.State.addIncrement, add_zero]
    exact d.covariance i j
  have hh := GaugeExcludedBounds.pressureAliasState_mean_bounds ActualPrimary.standardRegion
    (PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal)
    (PrimaryTargetBounds.radii_ordered ActualPrimary.nominal)
    (div_pos (FinalSlowBase.edgeExponent_pos ActualPrimary.nominal) (by norm_num)) zero_lt_one
    ActualPrimary.outgoing.data.h_pos (by norm_num : (1 : ℝ) ≠ 0)
    (CommonWindow.index ActualPrimary.h) (CommonWindow.gap ActualPrimary.h)
    (CommonWindow.native_le_index_add ActualPrimary.h ActualPrimary.outgoing.data.h_pos.le)
    BaseContextAssembly.slowScale BaseContextAssembly.one_le_slowScale (fun _ => le_max_right _ _)
    (ActualPrimary.commonContext B) (ActualInitialMean.ranked B N0)
    (ActualInitialCoherence.ranked_primitive B N0) d.operators d.base hu hW β
  dsimp only [GaugeExcludedBounds.actualGauge] at hh
  rw [← ActualInitialCoherence.commonGauge_eq_similarity] at hh
  exact hh

theorem initialAlias_all_gains_of_data (d : ActualInitialMean.PrimaryData B N0)
    (hu : CorrectionState.CumulativeBounds strip (ActualInitialMean.ranked B N0)) (β : ℝ) :
    MeanClass strip β (ActualInitialMean.initialAlias B N0) := by
  exact (temporalAlias_all_gains_of_primaryData d β).1.add
    (pressureAlias_all_gains_of_cumulative d hu β).1

/-- The two actual gauge aliases of the initialized state, with no
quantitative input assumptions on a residual or an alias. -/
theorem initialAlias_all_gains (B N0 : ℕ) (β : ℝ) :
    MeanClass strip β (ActualInitialMean.initialAlias B N0) :=
  initialAlias_all_gains_of_data (ActualInitialMean.primary_mean_data B N0)
    (ActualInitialMean.rank_bounds B N0).cumulative β

theorem initializedAlias_all_gains (B N0 : ℕ) (β : ℝ) :
    MeanClass gaussianStrip β (ActualInitialMean.initialized B N0).errors.aliasError := by
  have ht := (temporalAlias_all_gains_of_primaryData (ActualInitialMean.primary_mean_data B N0) β).2
  have hp := (pressureAlias_all_gains_of_cumulative (ActualInitialMean.primary_mean_data B N0)
    (ActualInitialMean.rank_bounds B N0).cumulative β).2
  have he : (ActualInitialMean.initialized B N0).errors.aliasError =
      VariableGaugeMean.temporalAliasState ActualPrimary.commonGauge ActualPrimary.h
        (CommonWindow.index ActualPrimary.h) (ActualPrimary.commonContext B)
            (ActualInitialMean.primary B N0) +
      VariableGaugeMean.pressureAliasState ActualPrimary.commonGauge (ActualPrimary.commonContext B)
        (ActualInitialMean.ranked B N0) := ActualInitialCoherence.initialized_aliases B N0
  rw [he]
  exact ht.add hp

theorem initializedAlias_unweighted (B N0 : ℕ) (β : ℝ) :
    UnweightedClass gaussianStrip β (ActualInitialMean.initialized B N0).errors.aliasError :=
  GaugeExcludedBounds.meanClass_unweighted (initializedAlias_all_gains B N0 β)
    (fun x _ => strip_zeta_le_one x.1)

end InitialAliases

section TotalExcluded

open CorrectionInitialization ActualPrimaryBounds

theorem initialized_errors_formula (B N0 : ℕ) :
    (ActualInitialMean.initialized B N0).errors.total =
      ActualBaseResidual.baseError ActualPrimary.certificate ActualPrimary.modulation
          ActualPrimary.upper B +
      initialGaussian B N0 + (ActualInitialMean.initialized B N0).errors.aliasError := by
  obtain ⟨hb, hg, _⟩ := GaugeInitialization.initializedBands_error_components
    ActualPrimary.commonGauge ActualPrimary.rankData ActualPrimary.h (CommonWindow.index
        ActualPrimary.h)
    ActualInitialMean.axial (ActualPrimary.commonContext B)
    (ActualPrimary.activeLabels ActualPrimary.standardRegion B N0) ActualInitialMean.primaryPiece
    (ActualInitialMean.baseError B)
  change (ActualInitialMean.initialized B N0).errors.base = _ at hb
  change (ActualInitialMean.initialized B N0).errors.gaussian = initialGaussian B N0 at hg
  simp only [CorrectionState.ExcludedErrors.total, hb, hg]
  rfl

/-- The remaining Gaussian premise is an estimate for the literal full
field; the base and both aliases in this formula are already constructed. -/
theorem initializedErrors_all_gains_of_gaussian (B N0 : ℕ) (β : ℝ) (i : Fin 3)
    (hg : UnweightedClass gaussianStrip β (fun n x => initialGaussian B N0 n x i)) :
    UnweightedClass gaussianStrip β (fun n x => (ActualInitialMean.initialized B N0).errors.total n
        x i) := by
  have hb := baseError_angle_component_class ActualPrimary.certificate ActualPrimary.modulation
    ActualPrimary.upper B ActualPrimary.standardRegion β i
  have ha := (initializedAlias_unweighted B N0 β).map (ContinuousLinearMap.proj i)
  apply WaveInteractionBounds.class_congr ((hb.add hg).add ha)
  intro n x _
  exact (congrArg (fun f => f n x i) (initialized_errors_formula B N0)).symm

end TotalExcluded

section ConstructedEndpoint

open CorrectionInitialization ActualPrimaryBounds

/-- All actual derivatives of the restored primary Gaussian field retain
the flat edge weight, uniformly over the whole label family. -/
theorem gaussianField_all_gains (B N0 : ℕ) (β : ℝ) (i : Fin 3) :
    LabelSumBounds.UniformClass gaussianStrip (fun _ _ x => Real.sqrt (strip.zeta x.1)) β
      (fun l : SignedLabel B N0 => fun n x => gaussianField l n x i) :=
  gaussianField_all_gains_of_carrier
    (ActualPhaseJetBounds.carrier_jets_cut (B := B) (N0 := N0)) β i

theorem initialGaussian_all_gains (B N0 : ℕ) (β : ℝ) (i : Fin 3) :
    MemClass gaussianStrip (fun _ x => Real.sqrt (strip.zeta x.1)) β
      (fun n x => initialGaussian B N0 n x i) :=
  initialGaussian_class_of_fields β i (gaussianField_all_gains B N0 β i)

theorem initialGaussian_unweighted (B N0 : ℕ) (β : ℝ) (i : Fin 3) :
    UnweightedClass gaussianStrip β (fun n x => initialGaussian B N0 n x i) :=
  initialGaussian_unweighted_of_fields β i (gaussianField_all_gains B N0 β i)

/-- The actual full excluded error of the literal initialized state has
every positive power (indeed every real power), on the whole angular and
free auxiliary lift. There is no supplied output-bound premise. -/
theorem initializedErrors_all_gains (B N0 : ℕ) (β : ℝ) (i : Fin 3) :
    UnweightedClass gaussianStrip β
      (fun n x => (ActualInitialMean.initialized B N0).errors.total n x i) :=
  initializedErrors_all_gains_of_gaussian B N0 β i (initialGaussian_unweighted B N0 β i)

theorem initializedErrors_vector_all_gains (B N0 : ℕ) (β : ℝ) :
    UnweightedClass gaussianStrip β (ActualInitialMean.initialized B N0).errors.total := by
  have h0 := (initializedErrors_all_gains B N0 β 0).map
    (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℝ) 0)
  have h1 := (initializedErrors_all_gains B N0 β 1).map
    (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℝ) 1)
  have h2 := (initializedErrors_all_gains B N0 β 2).map
    (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℝ) 2)
  apply WaveInteractionBounds.class_congr ((h0.add h1).add h2)
  intro n x _
  ext i
  fin_cases i <;> simp

end ConstructedEndpoint

end NavierStokes.ActualInitialExcluded

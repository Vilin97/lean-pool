/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleParameters

/-!
# The actual post-particular mean data

Only the particular wave is needed to prepare the signed request.  The
common assembly below is independent of a signed family or any signed
output estimate.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualParticularMeanGain

open Set Function Filter WeightedClasses MeanIncrementBounds CorrectionState CorrectionStep
open CorrectionInitialization VariableGaugeMean
open scoped ContDiff Topology BigOperators


/-- Point: an abbreviation for `ActualInitialization.Point`. -/
abbrev Point := ActualInitialization.Point
/-- Index: an abbreviation for `ActualInitialization.Index B N0`. -/
abbrev Index (B N0 : ℕ) := ActualInitialization.Index B N0

/-- Particular blocks: an abbreviation for `(ActualCycleParameters.fixedParameters B
N0).particularBlock x.coefficients (ActualPrimary.commonContext B) x.state`. -/
noncomputable abbrev particularBlocks {B N0 : ℕ} (x : CycleState (Index B N0)) :=
  (ActualCycleParameters.fixedParameters B N0).particularBlock x.coefficients
    (ActualPrimary.commonContext B) x.state

/-- Particular velocity: an abbreviation for `(ActualCycleParameters.fixedParameters B
N0).particularVelocity x.coefficients (ActualPrimary.commonContext B) x.state`. -/
noncomputable abbrev particularVelocity {B N0 : ℕ} (x : CycleState (Index B N0)) :=
  (ActualCycleParameters.fixedParameters B N0).particularVelocity x.coefficients
    (ActualPrimary.commonContext B) x.state

/-- Particular pressure: an abbreviation for `(ActualCycleParameters.fixedParameters B
N0).particularPressure x.coefficients (ActualPrimary.commonContext B) x.state`. -/
noncomputable abbrev particularPressure {B N0 : ℕ} (x : CycleState (Index B N0)) :=
  (ActualCycleParameters.fixedParameters B N0).particularPressure x.coefficients
    (ActualPrimary.commonContext B) x.state

/-- Particular gaussian: an abbreviation for `(ActualCycleParameters.fixedParameters B
N0).particularGaussian x.coefficients (ActualPrimary.commonContext B) x.state`. -/
noncomputable abbrev particularGaussian {B N0 : ℕ} (x : CycleState (Index B N0)) :=
  (ActualCycleParameters.fixedParameters B N0).particularGaussian x.coefficients
    (ActualPrimary.commonContext B) x.state

/-- Post particular: an abbreviation for `(ActualCycleParameters.fixedParameters B
N0).afterParticular x.coefficients (ActualPrimary.commonContext B) x.state`. -/
noncomputable abbrev postParticular {B N0 : ℕ} (x : CycleState (Index B N0)) :=
  (ActualCycleParameters.fixedParameters B N0).afterParticular x.coefficients
    (ActualPrimary.commonContext B) x.state

/-- Signed request: an abbreviation for `(ActualCycleParameters.fixedParameters B
N0).signedRequest x.coefficients (ActualPrimary.commonContext B) x.state`. -/
noncomputable abbrev signedRequest {B N0 : ℕ} (x : CycleState (Index B N0)) :=
  (ActualCycleParameters.fixedParameters B N0).signedRequest x.coefficients
    (ActualPrimary.commonContext B) x.state

/-- Label: an abbreviation for `ActualPrimaryCovariance.signedLabelOf l`. -/
noncomputable abbrev label {B N0 : ℕ} (_n : ℕ) (l : Index B N0) : SlotColoring.Label :=
  ActualPrimaryCovariance.signedLabelOf l

/-- First-wave data only.  These supports use the original selected slots
and physical window, independently of the signed output. -/
structure Inputs {B N0 : ℕ} (x : CycleState (Index B N0)) (σ : ℝ) : Prop where
  amplitude : ∀ i j, LabelSumBounds.UniformWaveClass ActualInitialization.strip
    ActualInitialization.envelope (1/2+σ)
    (fun l n z => (particularBlocks x l).velocity n i j z)
  smooth : WaveStateRegularity.AngularSmooth ActualInitialization.geometry.domain
      (particularVelocity x)
  periodic : OscillationPeriodic ActualPrimary.standardRegion.carrier (particularVelocity x)
  supported : WaveStateRegularity.WaveSupport ActualPrimary.standardRegion
    ActualInitialization.patch.a ActualInitialization.patch.b (particularVelocity x)
  old_support : LabelSumBounds.SupportedOscillations ActualPrimary.slots label
    ActualPrimaryCovariance.physicalWindow ActualPrimaryCovariance.absoluteAuxiliary
    ActualInitialization.strip.domain (fun l => (x.coefficients.blocks l).oscillation)
  particular_support : LabelSumBounds.SupportedOscillations ActualPrimary.slots label
    ActualPrimaryCovariance.physicalWindow ActualPrimaryCovariance.absoluteAuxiliary
    ActualInitialization.strip.domain (fun l => (particularBlocks x l).oscillation)

/-- All data needed before constructing the signed wave.  The covariance
and residual estimates are outputs of the actual first-wave update. -/
structure Result {B N0 : ℕ} (x : CycleState (Index B N0)) (σ : ℝ) : Prop where
  covariance : SignedMeanGain.TensorClass ActualInitialization.strip (1+σ)
    (SignedMeanGain.covarianceIncrement x.state.oscillation (particularVelocity x))
  covariance_moving : ∀ i j, GaugeMomentBalances.MovingField ActualPrimary.standardRegion
    ActualInitialization.patch.a ActualInitialization.patch.b
    (SignedMeanGain.covarianceIncrement x.state.oscillation (particularVelocity x) i j)
  primitive : MeanStateRegularity.PrimitiveData ActualPrimary.standardRegion
    ActualInitialization.patch.a ActualInitialization.patch.b (ActualPrimary.commonContext B)
    (postParticular x)
  reconstructed : reconstructState ActualPrimary.commonGauge (ActualPrimary.commonContext B)
    (postParticular x) = postParticular x
  pressure : MeanClass ActualInitialization.strip (1+σ-ChartScales.kappa)
    ((postParticular x).pressure - x.state.pressure)
  cumulative : CorrectionState.CumulativeBounds ActualInitialization.strip (postParticular x)
  theta : MeanClass ActualInitialization.strip (1+σ-ChartScales.kappa)
    ((postParticular x).thetaResidual (ActualPrimary.commonContext B))
  axial : MeanClass ActualInitialization.strip (1+σ-ChartScales.kappa)
    ((postParticular x).axialResidual (ActualPrimary.commonContext B))
  debt : DefectBounds ActualInitialization.slowStrip (σ-ChartScales.kappa)
    (ActualPrimary.commonContext B) (postParticular x)
  request : ∀ i, MeanClass (HarmonicWaveInteraction.productStrip ActualInitialization.strip)
    (σ-ChartScales.kappa) (fun n z => signedRequest x n z i)

section Gain

variable {B N0 : ℕ} {x : CycleState (Index B N0)} {σ : ℝ}
    {S : Index B N0 → ℕ → Set Point}
    (H : CycleAnalyticInvariant ActualInitialization.geometry (ActualPrimary.commonContext B)
      ActualInitialization.tangentBlock ActualInitialization.envelope S σ x)
    (d : Inputs x σ)

include H d

/-- Quantitative covariance of the literal first update, with uniform
constants obtained from the fixed slot assembly. -/
theorem covariance_class (hσ : 1 / 5 ≤ σ) :
    SignedMeanGain.TensorClass ActualInitialization.strip (1+σ)
      (SignedMeanGain.covarianceIncrement x.state.oscillation (particularVelocity x)) := by
  have hinj n : Set.InjOn (label (B := B) (N0 := N0) n) (x.coefficients.labels n : Set (Index B
      N0)) :=
    ActualPrimaryCovariance.signedLabelOf_injective.injOn
  have hlevel n (l : Index B N0) (_hl : l ∈ x.coefficients.labels n) : 1 ≤ (label n l).1 :=
    l.1.val.property.1
  have hrep : x.state.oscillation = LabelSumBounds.fieldSum x.coefficients.labels
      (fun l => (x.coefficients.blocks l).oscillation) := by
    funext n z i
    exact H.representation.velocity n z i
  have hcov := assembledCovarianceIncrement_mem (show (1:ℝ)/2 ≤ 1/2+σ by linarith)
    x.coefficients.labels label hinj hlevel ActualPrimaryCovariance.physicalWindow
    ActualPrimaryCovariance.physicalWindow_continuousOn ActualPrimaryCovariance.absoluteAuxiliary
    x.coefficients.blocks (particularBlocks x) x.coefficients.residualBand H.bands.velocityPressure
    ((ActualCycleParameters.fixedParameters B N0).particularBlock_band x.coefficients
      (ActualPrimary.commonContext B) x.state) (fun _ => ⟨rfl,rfl,rfl⟩)
    (fun i j _ => H.wave i j) (fun i j _ => d.amplitude i j) H.zeroVelocity
    ((ActualCycleParameters.fixedParameters B N0).particularBlock_zero x.coefficients
      (ActualPrimary.commonContext B) x.state)
    (fun l n z _ => ActualInitialization.envelope_nonneg l n z)
    (fun l n z _ => ActualInitialization.envelope_le_one l n z)
    H.angular d.old_support d.particular_support x.state hrep
  simp only [show (1:ℝ)/2+(1/2+σ) = 1+σ by ring] at hcov ⊢
  exact hcov

theorem covariance_moving : ∀ i j, GaugeMomentBalances.MovingField ActualPrimary.standardRegion
    ActualInitialization.patch.a ActualInitialization.patch.b
    (SignedMeanGain.covarianceIncrement x.state.oscillation (particularVelocity x) i j) :=
  covarianceIncrement_moving ActualPrimary.standardRegion H.oscillationSmooth d.smooth d.supported
    H.oscillationPeriodic d.periodic

/-- Prepare the actual signed request without any signed-wave estimate
or complete four-stage input record. -/
theorem postParticular_gain (hσ : 1 / 5 ≤ σ) : Result x σ := by
  have hCov := covariance_class H d hσ
  have hMove := covariance_moving H d
  have hPr := H.primitives.waveStage ActualPrimary.commonGauge (particularVelocity x)
    (particularPressure x) (particularGaussian x) hMove
  have hRec : reconstructState ActualPrimary.commonGauge (ActualPrimary.commonContext B)
      (postParticular x) = postParticular x :=
    GaugeMomentBalances.reconstructState_idempotent _ _ _
  have hFixed : (reconstructState ActualPrimary.commonGauge (ActualPrimary.commonContext B)
      x.state).pressure = x.state.pressure :=
    congrArg (fun u : State Point => u.pressure) H.reconstructed
  obtain ⟨hθ, hz⟩ := H.raw_mean_bounds
  obtain ⟨hp, hcum, htheta, haxial, hdebt, hrequest⟩ := waveStage_mean_gain
      ActualInitialization.geometry
    (ActualPrimary.commonContext B) x.state (particularVelocity x) (particularPressure x)
    (particularGaussian x) hσ (ActualInitialization.operators B).kappa_nonneg
    (show ChartScales.kappa ≤ 1/100000 by rfl) H.primitives (ActualInitialization.operators B)
    (ActualInitialization.base_bounds B) H.cumulative hFixed hθ hz H.debt hMove hCov
  exact ⟨hCov, hMove, hPr, hRec, hp, hcum, htheta, haxial, hdebt, hrequest⟩

end Gain

end NavierStokes.ActualParticularMeanGain

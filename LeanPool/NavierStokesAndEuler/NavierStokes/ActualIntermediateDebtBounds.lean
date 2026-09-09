/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularMeanGain
public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectionAnalyticStep

@[expose] public section

/-!
# Measured debt before the actual rank correction

The first-wave debt, the signed covariance change, and the temporal mean
change are evaluated on the literal intermediate states.  No estimate of
the post-temporal debt is supplied as a premise.
-/

noncomputable section

namespace NavierStokes.ActualIntermediateDebtBounds

open Set Function WeightedClasses MeanIncrementBounds CorrectionState CorrectionStep
open CorrectionInitialization VariableGaugeMean
open scoped ContDiff Topology BigOperators


abbrev Point := ActualInitialization.Point
abbrev Index (B N0 : ℕ) := ActualInitialization.Index B N0

noncomputable abbrev signedVelocity {B N0 : ℕ} (x : CycleState (Index B N0)) :=
  (ActualCycleParameters.fixedParameters B N0).signedVelocity x.coefficients
    (ActualPrimary.commonContext B) x.state

noncomputable abbrev signedPressure {B N0 : ℕ} (x : CycleState (Index B N0)) :=
  (ActualCycleParameters.fixedParameters B N0).signedPressure x.coefficients
    (ActualPrimary.commonContext B) x.state

noncomputable abbrev signedGaussian {B N0 : ℕ} (x : CycleState (Index B N0)) :=
  (ActualCycleParameters.fixedParameters B N0).signedGaussian x.coefficients
    (ActualPrimary.commonContext B) x.state

noncomputable abbrev postSigned {B N0 : ℕ} (x : CycleState (Index B N0)) :=
  (ActualCycleParameters.fixedParameters B N0).afterSigned x.coefficients
    (ActualPrimary.commonContext B) x.state

noncomputable abbrev temporalIncrement {B N0 : ℕ} (x : CycleState (Index B N0)) :=
  (ActualCycleParameters.fixedParameters B N0).temporalIncrement x.coefficients
    (ActualPrimary.commonContext B) x.state

noncomputable abbrev postTemporal {B N0 : ℕ} (x : CycleState (Index B N0)) :=
  (ActualCycleParameters.fixedParameters B N0).afterTemporal x.coefficients
    (ActualPrimary.commonContext B) x.state

section Core

variable {B N0 : ℕ} {x : CycleState (Index B N0)} {σ : ℝ}
    {S : Index B N0 → ℕ → Set Point}
    (H : CycleAnalyticInvariant ActualInitialization.geometry (ActualPrimary.commonContext B)
      ActualInitialization.tangentBlock ActualInitialization.envelope S σ x)
    (hσ : 1/5 ≤ σ)
    (first : ActualParticularMeanGain.Result x σ)
    (hCov : SignedMeanGain.TensorClass ActualInitialization.strip (1+σ-ChartScales.kappa)
      (SignedMeanGain.covarianceIncrement (ActualParticularMeanGain.postParticular x).oscillation
        (signedVelocity x)))
    (hX : ∀ i j, GaugeMomentBalances.MovingField ActualPrimary.standardRegion
      ActualInitialization.patch.a ActualInitialization.patch.b
      (SignedMeanGain.covarianceIncrement (ActualParticularMeanGain.postParticular x).oscillation
        (signedVelocity x) i j))
    (hTemporal : IncrementBounds ActualInitialization.strip (1+σ-2*ChartScales.kappa)
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
    simp only [show (1+σ-ChartScales.kappa)-ChartScales.kappa = 1+σ-2*ChartScales.kappa by ring] at
      hSigned
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
    (hσ : 1/5 ≤ σ) (particular : ActualParticularMeanGain.Inputs x σ)
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

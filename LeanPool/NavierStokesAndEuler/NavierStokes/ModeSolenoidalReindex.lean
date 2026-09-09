/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.StateReindex
public import LeanPool.NavierStokesAndEuler.NavierStokes.HarmonicWaveInteraction

@[expose] public section

/-!
# Actual harmonic divergence under a change of product association

The same complex single-mode field is pulled back along the cylinder
isometry. Its genuine cylindrical divergence is preserved, including the
transported radial and axial directions. No new divergence premise is
needed for the associated particular-solver coordinates.
-/

noncomputable section

namespace NavierStokes.ModeSolenoidalReindex

open HarmonicCalculus WeightedClasses

variable {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem amplitude_pull (e : D ≃ₗᵢ[ℝ] E) (b : CorrectionState.HarmonicBlock E)
    (j : ℤ) (n : ℕ) :
    HarmonicWaveInteraction.amplitude (StateReindex.block e b) j n =
      fun x => HarmonicWaveInteraction.amplitude b j n (e x) := by
  funext x i
  simp only [HarmonicWaveInteraction.amplitude, HarmonicMeanInteraction.blockAmplitude,
    StateReindex.block, StateReindex.realCoefficients_pull, StateReindex.coefficients_apply]

theorem singleMode_pull (e : D ≃ₗᵢ[ℝ] E) (b : CorrectionState.HarmonicBlock E)
    (j : ℤ) (n : ℕ) :
    HarmonicWaveInteraction.singleMode (StateReindex.block e b) j n =
      fun x => HarmonicWaveInteraction.singleMode b j n (StateReindex.cylinder e x) := by
  funext x i
  simp only [HarmonicWaveInteraction.singleMode, HarmonicResidual.vectorField,
    HarmonicFields.field, HarmonicFields.evaluate_single,
    HarmonicWaveInteraction.amplitude, HarmonicMeanInteraction.blockAmplitude,
    StateReindex.block, StateReindex.realCoefficients_pull,
    StateReindex.coefficients_apply, StateReindex.cylinder_apply]

theorem liftDirection_pull (e : D ≃ₗᵢ[ℝ] E) (V : E → E) :
    HarmonicResidual.liftDirection (StateReindex.vector e V) =
      StateReindex.vector (StateReindex.cylinder e) (HarmonicResidual.liftDirection V) := by
  funext x
  simp only [HarmonicResidual.liftDirection, StateReindex.vector,
    ParticularWaveBounds.reindexVector, StateReindex.cylinder_apply,
    StateReindex.cylinder_symm_apply]

theorem angularDirection_pull (e : D ≃ₗᵢ[ℝ] E) :
    StateReindex.vector (StateReindex.cylinder e)
      (HarmonicResidual.angularDirection (D := E)) = HarmonicResidual.angularDirection := by
  funext x
  change (e.symm 0, (1 : ℝ)) = (0, 1)
  rw [map_zero]

theorem cylindricalDivergence_pull (e : D ≃ₗᵢ[ℝ] E) (R : E → ℝ)
    (Vr Vθ Vz : E → E) (a : E → ComplexVector) (x : D) :
    cylindricalDivergence (fun y => R (e y)) (StateReindex.vector e Vr)
      (StateReindex.vector e Vθ) (StateReindex.vector e Vz) (fun y => a (e y)) x =
      cylindricalDivergence R Vr Vθ Vz a (e x) := by
  simp only [cylindricalDivergence, StateReindex.along_pull_component]

theorem singleMode_divergence_pull (e : D ≃ₗᵢ[ℝ] E)
    (c : CorrectionState.Context E) (b : CorrectionState.HarmonicBlock E)
    (j : ℤ) (n : ℕ) (p : D × ℝ) :
    cylindricalDivergence (fun q => (StateReindex.context e c).operators.radius q.1)
      (HarmonicResidual.liftDirection
        (HarmonicResidual.contextFrame (StateReindex.context e c) n).radial)
      HarmonicResidual.angularDirection
      (HarmonicResidual.liftDirection
        (HarmonicResidual.contextFrame (StateReindex.context e c) n).axial)
      (HarmonicWaveInteraction.singleMode (StateReindex.block e b) j n) p =
    cylindricalDivergence (fun q => c.operators.radius q.1)
      (HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).radial)
      HarmonicResidual.angularDirection
      (HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).axial)
      (HarmonicWaveInteraction.singleMode b j n) (StateReindex.cylinder e p) := by
  rw [StateReindex.contextFrame_pull, singleMode_pull]
  change cylindricalDivergence (fun q => c.operators.radius (e q.1))
    (HarmonicResidual.liftDirection (StateReindex.vector e (HarmonicResidual.contextFrame c
      n).radial))
    HarmonicResidual.angularDirection
    (HarmonicResidual.liftDirection (StateReindex.vector e (HarmonicResidual.contextFrame c
      n).axial))
    (fun q => HarmonicWaveInteraction.singleMode b j n (StateReindex.cylinder e q)) p = _
  rw [liftDirection_pull, liftDirection_pull, ← angularDirection_pull e]
  exact cylindricalDivergence_pull (StateReindex.cylinder e)
    (fun q : E × ℝ => c.operators.radius q.1)
    (HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).radial)
    HarmonicResidual.angularDirection
    (HarmonicResidual.liftDirection (HarmonicResidual.contextFrame c n).axial)
    (HarmonicWaveInteraction.singleMode b j n) p

theorem modeSolenoidal_pull (e : D ≃ₗᵢ[ℝ] E) {s : StripData E}
    {c : CorrectionState.Context E} {b : CorrectionState.HarmonicBlock E}
    (hb : HarmonicWaveInteraction.ModeSolenoidal s c b) :
    HarmonicWaveInteraction.ModeSolenoidal (ParticularWaveBounds.reindexStrip e s)
      (StateReindex.context e c) (StateReindex.block e b) := by
  intro j hj n p hp
  rw [singleMode_divergence_pull]
  exact hb j hj n (StateReindex.cylinder e p) hp

end NavierStokes.ModeSolenoidalReindex

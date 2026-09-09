/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryBudget
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryPaths
import LeanPool.NavierStokesAndEuler.Euler.PacketInitialAmplitude
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryHomogeneity
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryUnitBounds

/-!
The actual primary A/g and A_t/g retain one fixed mixed Sobolev radius.
The constants and guards depend only on source coefficients, the history
length and the genuine propagator bound. Arbitrary terminal amplitude is
restored by the proved exact homogeneity of the constructed solution.
-/

@[expose] public section


noncomputable section

namespace EulerTransversePacketPrimary.Budget

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerTransversePacketProvider EulerParameterWordGevrey EulerGevrey EulerContinuousTimeWeight
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)} {ι : Type*} [Fintype ι] {q : ℕ}
  {L : EulerTransversePacketJoin.Budget D τ hτ hτT B ι q}
  (H : Budget L) (Y : InitialData P D)
  (directions : ι → LiftTangent) (hdir : ∀ i, ‖directions i‖ ≤ 1)
  (A : ℝ) (hA : 0 ≤ A) (d : ℕ)
  (hYb : ∀ n, block directions q (fun a => translate P a (Y.value : CylinderL2 P U)) n 0 ≤
    A * majorant L.R d n)

include hdir hA hYb

theorem velocity_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (velocityPath τ hτ hτT B Y))) n 0 ≤
        (H.velocityCost*A)*majorant L.R (d+3) n :=
  initial_amplitude_bound (fun Z => velocityPath τ hτ hτT B Z)
    (velocityPath_orbit τ hτ hτT B) (velocityPath_eq_smul τ hτ hτT B)
    L.fullProfile L.fullProfile_pos directions q L.R H.velocityCost d (d+3)
    (fun Z hb => H.velocity_unit_bound Z directions hdir d hb) Y A hA hYb n

theorem derivative_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (derivativePath τ hτ hτT B Y))) n 0 ≤
        (H.derivativeCost*A)*majorant L.R (d+3) n :=
  initial_amplitude_bound (fun Z => derivativePath τ hτ hτT B Z)
    (derivativePath_orbit τ hτ hτT B) (derivativePath_eq_smul τ hτ hτT B)
    L.fullProfile L.fullProfile_pos directions q L.R H.derivativeCost d (d+3)
    (fun Z hb => H.derivative_unit_bound Z directions hdir d hb) Y A hA hYb n

end EulerTransversePacketPrimary.Budget

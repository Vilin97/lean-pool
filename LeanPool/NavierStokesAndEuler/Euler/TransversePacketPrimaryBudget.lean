/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketBudget
public import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointBounds

@[expose] public section

/-!
Additional source-only radius guards for the primary endpoint history.
The forced-profile budget supplies the original coefficient and propagator
bounds. These extra guards use only the unit terminal-data cost, never the
terminal amplitude or a recursive derivative shift.
-/

noncomputable section

namespace EulerTransversePacketPrimary

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerTransversePacketProvider
  EulerTimeIntervalRestriction EulerGevrey EulerParameterWordGevrey EulerTransverseFixedSobolev
  EulerTimeLpGramSobolev EulerTimeLpAccelerationSobolev EulerFixedEvolutionSobolev
  EulerCylinderDirichlet.Coefficients EulerSourceCylinderForwardSobolev
    EulerSourceCylinderTimeBounds
  EulerLinearDuhamel
open scoped ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)} {ι : Type*} [Fintype ι] {q : ℕ}
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B ι q)

structure Budget where
  history_weak :
    2*blockCost ι q τ L.Rc L.C₀ L.C₁ L.CH (D.initial τ hτ hτT.le).frameLower
      (endpointForcingCost ι q τ L.Rc L.C₁)*(sobolevCoefficientRadius ι L.Rc+1) ≤ L.R
  history_strong :
    2*gramBlockCost ι q (D.initial τ hτ hτT.le).frameLower L.Rc L.C₀
      (accelerationBlockAmplitude ι q L.Rc L.C₀ L.C₁ (endpointForcingCost ι q τ L.Rc L.C₁) 1)*
        (sobolevCoefficientRadius ι L.Rc+1) ≤ L.R
  history_uniform :
    2*gramBlockCost ι q (D.initial τ hτ hτT.le).frameLower L.Rc L.C₀
      (accelerationBlockAmplitude ι q L.Rc L.C₀ L.C₁
        (endpointForcingCost ι q τ L.Rc L.C₁) (traceCost τ))*
          (sobolevCoefficientRadius ι L.Rc+1) ≤ L.R
  forward_radius :
    2*forwardSobolevCost ι q (D.T-τ) L.C (τ⁻¹+traceCost τ)
      (forcingCost ι q L.Ri L.C₀*0)
      (18*L.Ri*L.C₀*L.C₁) (4*L.Ri)*(sobolevCoefficientRadius ι (4*L.Ri)+1) ≤ L.R

namespace Budget

variable {L} (H : Budget L)

def endpointBudget : EndpointBudget B.coefficients ι q where
  Rc := L.Rc
  C₀ := L.C₀
  C₁ := L.C₁
  CH := L.CH
  R := L.R
  Rc_nonneg := L.Rc_nonneg
  C₀_nonneg := L.C₀_nonneg
  C₁_nonneg := L.C₁_nonneg
  CH_nonneg := L.CH_nonneg
  time_le_one := L.history_length
  frame_smooth := (D.initial τ hτ hτT.le).frame.translation_contDiff
  frameDerivative_smooth := (D.initial τ hτ hτT.le).frameDerivative.translation_contDiff
  hessian_smooth := B.H.translation_contDiff
  frame_bound n a := (D.initial τ hτ hτT.le).frame.norm_iteratedFDeriv_translation_le n _
    (mul_nonneg L.C₀_nonneg (majorant_nonneg L.Rc L.Rc_nonneg 0 n))
    ((D.initial τ hτ hτT.le).frame_spatial_bound n _
      (fun t x => L.frame_bound n (initialInclusion D.T τ hτT.le t) x)) a
  frameDerivative_bound n a := (D.initial τ hτ
    hτT.le).frameDerivative.norm_iteratedFDeriv_translation_le n _
    (mul_nonneg L.C₁_nonneg (majorant_nonneg L.Rc L.Rc_nonneg 0 n))
    ((D.initial τ hτ hτT.le).frameDerivative_spatial_bound n _
      (fun t x => L.frameDerivative_bound n (initialInclusion D.T τ hτT.le t) x)) a
  hessian_bound n a := B.H.norm_iteratedFDeriv_translation_le n _
    (mul_nonneg L.CH_nonneg (majorant_nonneg L.Rc L.Rc_nonneg 0 n)) (L.hessian_bound n) a
  weak_radius := H.history_weak
  strong_radius := H.history_strong
  uniform_radius := H.history_uniform

def velocityCost : ℝ := H.endpointBudget.velocityCost + 3*sobolevCoefficientAmplitude ι q L.Rc L.C₀

def derivativeCost : ℝ := H.endpointBudget.derivativeCost + physicalCost ι q L.Ri L.C₀ L.C₁ 0 1

theorem velocityCost_nonneg : 0 ≤ H.velocityCost := by
  have hC := sobolevCoefficientAmplitude_nonneg (ι := ι) q L.Rc L.C₀ L.Rc_nonneg L.C₀_nonneg
  have hA := H.endpointBudget.coordinateCost_nonneg
  change 0 ≤ 3*sobolevCoefficientAmplitude ι q L.Rc L.C₀*H.endpointBudget.coordinateCost+
    3*sobolevCoefficientAmplitude ι q L.Rc L.C₀
  positivity

end Budget
end EulerTransversePacketPrimary

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceGeometryData
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketLabelData
import LeanPool.NavierStokesAndEuler.Euler.ParentPacketScaledBounds

/-! Actual selected terminal coordinates and the canonical boundary
parameter have fixed polynomial caps. They are inputs to the uniform
normal-stage source envelope. -/

@[expose] public section


noncomputable section

namespace EulerParentPacketParameterCaps

open Real EulerPacketParentLabelBounds EulerTransverseActivationSelection EulerMeanHarmonic

/-- Terminal constant, given by `8*(activationConstant CM CH+1)*(1+3*(1+embeddingCost)^2)`. -/
def terminalConstant (CM CH : ℝ) : ℝ :=
  8*(activationConstant CM CH+1)*(1+3*(1+embeddingCost)^2)

theorem terminalConstant_nonneg (CM CH : ℝ) (hCH : 0 ≤ CH) :
    0 ≤ terminalConstant CM CH := by
  unfold terminalConstant activationConstant
  positivity

/-- Boundary constant, given by `boundaryLocalizationC1*(CM+2)+1`. -/
def boundaryConstant (CM : ℝ) : ℝ := boundaryLocalizationC1*(CM+2)+1

theorem boundaryConstant_pos (CM : ℝ) (hCM : 0 ≤ CM) : 0 < boundaryConstant CM := by
  unfold boundaryConstant
  positivity [boundaryLocalizationC1_nonneg]

theorem boundary_parameter_bound (CM Bc L X : ℝ) (hX : 1 ≤ X)
    (hBc : Bc ≤ CM * X ^ 1000 + 2) (hL : L = boundaryLocalizationC1 * Bc + 1) :
    L ≤ boundaryConstant CM*X^1000 := by
  have hp : 1 ≤ X^1000 := one_le_pow₀ hX
  have hb : Bc ≤ (CM+2)*X^1000 := by nlinarith only [hBc,hp]
  have h := mul_le_mul_of_nonneg_left hb boundaryLocalizationC1_nonneg
  rw [hL]
  unfold boundaryConstant
  nlinarith only [h,hp]

end EulerParentPacketParameterCaps

namespace EulerParentPacketFrames.LabelData

open Set EulerSmoothLimit EulerTransverseFrameCoordinates EulerTransversePacketProvider
  EulerPacketSourceGeometry EulerPacketParentLabelBounds EulerGevrey
  EulerParentPacketParameterCaps EulerTransverseActivationSelection

variable {A : Parent} (L : LabelData A)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hsupport : IsCompact support)
  {τ : ℝ} {hτ : 0 < τ} {hτT : τ < A.T}
  {P : ParentFrame (A.transverseData m hm R support hsupport) τ}
  {H : HistoryData ((A.transverseData m hm R support hsupport).initial τ hτ hτT.le)}
  (G : Guards hτ hτT P H)

theorem selected_terminal_bound (hH : 1 ≤ P.shear) :
    ‖G.terminal‖ ≤ terminalConstant G.CM G.CH*L.K^4 := by
  let D := A.transverseData m hm R support hsupport
  have hK0 := zero_le_one.trans L.K_one
  have hF : ∀ t x, ‖D.F.field t x‖ ≤ frameAmplitude L.K := by
    intro t x
    change ‖A.frame.field t x‖ ≤ frameAmplitude L.K
    have h := L.frame_scaled_bound 0 t x
    simpa only [norm_iteratedFDeriv_zero,majorant,Nat.zero_add,Nat.factorial_zero,
      Nat.cast_one,pow_zero,mul_one,one_pow] using h
  have hInv := D.inverseBound_le_of_frame (frameAmplitude L.K)
    (frameAmplitude_nonneg L.K) A.frame_det hF
  have hK2 : 1 ≤ L.K^2 := one_le_pow₀ L.K_one
  have hK4 : 1 ≤ L.K^4 := one_le_pow₀ L.K_one
  have hEmb := embeddingCost_nonneg
  have hFcap : frameAmplitude L.K ≤ (1+embeddingCost)*L.K^2 := by
    unfold frameAmplitude gradientAmplitude
    nlinarith only [hK2]
  have hFsquare := pow_le_pow_left₀ (frameAmplitude_nonneg L.K) hFcap 2
  have hIcap : D.inverseBound ≤ (1+3*(1+embeddingCost)^2)*L.K^4 := by
    nlinarith only [hInv,hFsquare,hK4]
  have hAct : 0 ≤ 8*(activationConstant G.CM G.CH+1) := by
    unfold activationConstant
    positivity [G.CH_nonneg]
  calc
    _ ≤ P.terminalBound G.CM G.CH := G.terminal_properties.2.2.2.1
    _ ≤ 8*(activationConstant G.CM G.CH+1)*D.inverseBound := by
      unfold ParentFrame.terminalBound
      exact div_le_self (mul_nonneg hAct D.inverseBound_pos.le) hH
    _ ≤ 8*(activationConstant G.CM G.CH+1)*((1+3*(1+embeddingCost)^2)*L.K^4) :=
      mul_le_mul_of_nonneg_left hIcap hAct
    _ = _ := by unfold terminalConstant; ring

end EulerParentPacketFrames.LabelData

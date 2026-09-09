/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentInitializedUniformCosts
public import LeanPool.NavierStokesAndEuler.Euler.ParentForwardUniformCosts
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketParameterCaps
public import LeanPool.NavierStokesAndEuler.Euler.PacketLowConstants
public import LeanPool.NavierStokesAndEuler.Euler.PacketUniformFrequencyScales

@[expose] public section

/-! The actual normal-stage source size is controlled by one fixed
envelope. This includes the chosen terminal coordinate and canonical
boundary coefficient, with the polynomial first shear retained. -/

noncomputable section

namespace EulerNormalPacketParameters

open Real EulerPacketLowConstants EulerParentPacketParameterCaps
  EulerPacketUniformFrequencyScales EulerPacketUniformSource EulerPacketSourceFrequency
  EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence EulerPacketSourceParameterScales

def terminalCap : ℝ := 1+terminalConstant gradientConstant hessianConstant
def sourceConstant (C : ℝ) : ℝ :=
  EulerPacketParameterEnvelope.boundConstant C (boundaryConstant gradientConstant) terminalCap

theorem terminalCap_one : 1 ≤ terminalCap := by
  have h := terminalConstant_nonneg gradientConstant hessianConstant hessian_nonneg
  unfold terminalCap
  linarith only [h]

theorem sourceConstant_pos (C : ℝ) : 0 < sourceConstant C :=
  EulerPacketParameterEnvelope.constant_pos C (boundaryConstant gradientConstant) terminalCap
    (boundaryConstant_pos gradientConstant gradient_nonneg).le (zero_le_one.trans terminalCap_one)

def envelope (J : ℕ) (C X : ℝ) (n : ℕ) : ℝ := parameterEnvelope J (sourceConstant C) 320 20 1000 X n

def frequencySpec (C : ℝ) : CostSpec :=
  frequencyCostSpec (1+frequencyConstant) (sourceConstant C) 320
    (by have h := frequencyConstant_pos; linarith) (sourceConstant_pos C)
    20 1000 (frequencyPower+1) (theta/100) (by norm_num [theta])

theorem previousShear_one (J : ℕ) (hJ : 1 ≤ J) (X : ℝ) (hX : 1 ≤ X) (n : ℕ) :
    1 ≤ previousShear J X n := by
  cases n with
  | zero => exact one_le_pow₀ hX
  | succ n =>
    apply one_le_exp
    have hx := sequence_one_le J hJ X hX n
    exact div_nonneg (zero_le_one.trans hx) (by positivity)

theorem frequency_guard (J : ℕ) (C X P : ℝ) (n : ℕ)
    (hP : 1 ≤ P) (hPE : P ≤ envelope J C X n)
    (hcost : (frequencySpec C).cost J (scaleSequence J X) n ≤ 1) :
    frequencyConstant*P^frequencyPower ≤ smallPower (frequency J X n) := by
  have hE : 1 ≤ envelope J C X n := hP.trans hPE
  have hguard := guard_of_cost_le J (1+frequencyConstant) (sourceConstant C) 320
    (by have h := frequencyConstant_pos; linarith) (sourceConstant_pos C)
    20 1000 (frequencyPower+1) (theta/100) (by norm_num [theta]) X n hcost
  apply le_trans _ hguard
  have hpow := pow_le_pow_left₀ (zero_le_one.trans hP) hPE frequencyPower
  have hstep := pow_le_pow_right₀ hE (Nat.le_add_right frequencyPower 1)
  have hC := frequencyConstant_pos.le
  calc
    _ ≤ frequencyConstant*(envelope J C X n)^frequencyPower := mul_le_mul_of_nonneg_left hpow hC
    _ ≤ (1+frequencyConstant)*(envelope J C X n)^(frequencyPower+1) :=
      mul_le_mul (le_add_of_nonneg_left zero_le_one) hstep
        (pow_nonneg (zero_le_one.trans hE) _) (add_nonneg zero_le_one hC)

end EulerNormalPacketParameters

namespace EulerParentPacketFrames.LabelData

open Set Real EulerSmoothLimit EulerTransverseFrameCoordinates EulerTransversePacketProvider
  EulerPacketSourceGeometry EulerPacketSourceScales EulerPacketSourceScaleChoice
  EulerPacketSourceScaleSequence EulerPacketBaseGuardScales EulerPacketLowConstants
  EulerParentPacketParameterCaps EulerNormalPacketParameters

variable {A : Parent} (L : LabelData A) (H : LowBounds A)
  {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (m : Space) (hm : ‖m‖=1) (R : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hsupport : IsCompact support)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < A.T)
  (P : ParentFrame (A.transverseData m hm R support hsupport) τ)
  (G : Guards hτ hτT P (A.historyOn H m hm R support hsupport τ hτ hτT))

theorem normalParameterSize_bound (J D : ℕ) (hJ : 2 ≤ J) (C X : ℝ) (hC : 1 ≤ C) (hX : 1 ≤ X)
    (n : ℕ) (Ti TiTotal : ℝ)
    (hbaseH : X^1000 ≤ exp (X/((J-1 : ℕ) : ℝ)^7))
    (hbaseK : X^D ≤ exp (X/((J-1 : ℕ) : ℝ)^4))
    (hK : L.K ≤ previousFrequency J D X n^80)
    (hTi : Ti ≤ 12/baseHorizon J X) (hTiTotal : TiTotal ≤ 12/baseHorizon J X)
    (hBc : H.Bc ≤ gradientConstant*X^1000+2)
    (hL : H.L=EulerMeanHarmonic.boundaryLocalizationC1*H.Bc+1)
    (hM : G.CM=gradientConstant) (hH : G.CH=hessianConstant)
    (hΘ : P.horizon ≤ sourceTheta J C (scaleSequence J X) n)
    (hδ : G.δ=spike J X n) (hh : G.hchild=shear J X n)
    (hshear : P.shear=previousShear J X n) :
    L.geometryParameterSize H m hm R support hsupport τ hτ hτT P G Ti TiTotal G.terminal ≤
      envelope J C X n := by
  have hprev : 1 ≤ P.shear := hshear.symm ▸ previousShear_one J (by omega) X hX n
  have hterm := L.selected_terminal_bound m hm R support hsupport G hprev
  rw [hM,hH] at hterm
  have hterm' : ‖G.terminal‖ ≤ terminalCap*L.K^4 := hterm.trans
    (mul_le_mul_of_nonneg_right (by unfold terminalCap; linarith) (pow_nonneg (zero_le_one.trans
      L.K_one) _))
  have hboundary := boundary_parameter_bound gradientConstant H.Bc H.L X hX hBc hL
  have hEi : P.epsilon⁻¹ ≤ 2*previousShear J X n := by
    rw [← hshear]
    exact P.epsilon_inv_le_twice_shear G.coupling_lower hprev
  have hraw := EulerPacketParameterEnvelope.source_size_le J D hJ X hX
    C (boundaryConstant gradientConstant) terminalCap 80 320 hC
    (boundaryConstant_pos gradientConstant gradient_nonneg).le (zero_le_one.trans terminalCap_one)
    (by norm_num) (by norm_num) (by norm_num) 4 (by norm_num) hbaseH hbaseK n
    L.K Ti TiTotal (560*P.horizon^10/P.epsilon) H.L ‖G.terminal‖ P.horizon P.epsilon⁻¹
    (zero_le_one.trans L.K_one) (by simpa only [rpow_ofNat] using hK)
    hTi hTiTotal hboundary hterm' (zero_le_one.trans G.horizon_lower) hΘ
    (inv_nonneg.mpr G.epsilon_pos.le) hEi (by rw [div_eq_mul_inv])
  change EulerParentInitializedRadius.parameterSize L.K Ti TiTotal (560*P.horizon^10/P.epsilon)
    H.L G.δ ‖G.terminal‖+G.hchild ≤ _
  rw [hδ,hh]
  exact hraw

end EulerParentPacketFrames.LabelData

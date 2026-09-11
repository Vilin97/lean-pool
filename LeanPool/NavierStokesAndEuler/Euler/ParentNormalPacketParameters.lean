/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.ParentInitializedUniformCosts
public import LeanPool.NavierStokesAndEuler.Euler.PacketLowConstants
import LeanPool.NavierStokesAndEuler.Euler.PacketSourceParameterScales
import LeanPool.NavierStokesAndEuler.Euler.ParentPacketNeighborPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceGeometryData
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketLabelData
import LeanPool.NavierStokesAndEuler.Euler.ParentPacketScaledBounds
public import LeanPool.NavierStokesAndEuler.Euler.ParentInitializedRadiusPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.PacketBaseGuardScales
public import LeanPool.NavierStokesAndEuler.Euler.PacketUniformFrequencyScales

/-! The actual normal-stage source size is controlled by one fixed
envelope. This includes the chosen terminal coordinate and canonical
boundary coefficient, with the polynomial first shear retained. -/

section

/-! The source size used by the canonical packet solve is bounded by
one explicit polynomial-exponential envelope, including the base-sized
boundary coefficient and both reciprocal time intervals. -/

@[expose] public section

noncomputable section

namespace EulerPacketParameterEnvelope

open Real EulerPacketSourceParameterScales EulerPacketUniformFrequencyScales
  EulerPacketSourceScaleSequence EulerPacketSourceScaleChoice EulerParentInitializedRadius
  EulerPacketSourceScales

/-- Bound constant, given by `8+1120*(2*Cθ)^10+CB+Cξ`. -/
def boundConstant (Cθ CB Cξ : ℝ) : ℝ := 8+1120*(2*Cθ)^10+CB+Cξ

theorem constant_pos (Cθ CB Cξ : ℝ) (hB : 0 ≤ CB) (hξ : 0 ≤ Cξ) :
    0 < boundConstant Cθ CB Cξ := by
  unfold boundConstant
  positivity

theorem source_size_le (J D : ℕ) (hJ : 2 ≤ J) (X : ℝ) (hX : 1 ≤ X)
    (Cθ CB Cξ d c : ℝ) (hθ : 1 ≤ Cθ) (hB : 0 ≤ CB) (hξC : 0 ≤ Cξ)
    (hd : 0 ≤ d) (hc : 1 ≤ c) (hdc : d ≤ c)
    (R : ℕ) (hRc : (R : ℝ) * d ≤ c)
    (hbaseH : X ^ 1000 ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 7))
    (hbaseK : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4))
    (n : ℕ) (K Ti TiTotal Cp B ξ Θ Ei : ℝ) (hK0 : 0 ≤ K)
    (hK : K ≤ previousFrequency J D X n ^ d)
    (hTi : Ti ≤ 12 / EulerPacketBaseGuardScales.baseHorizon J X)
    (hTiTotal : TiTotal ≤ 12 / EulerPacketBaseGuardScales.baseHorizon J X)
    (hBc : B ≤ CB * X ^ 1000) (hξ : ξ ≤ Cξ * K ^ R)
    (hΘ0 : 0 ≤ Θ) (hΘ : Θ ≤ sourceTheta J Cθ (scaleSequence J X) n)
    (hEi0 : 0 ≤ Ei) (hEi : Ei ≤ 2 * previousShear J X n)
    (hCp : Cp ≤ 560 * Θ ^ 10 * Ei) :
    parameterSize K Ti TiTotal Cp B (spike J X n) ξ+shear J X n ≤
      parameterEnvelope J (boundConstant Cθ CB Cξ) c 20 1000 X n := by
  let z := predecessorExponent J X n
  let E := exp (c*z)
  let F := polynomialFactor J X n
  have hz : 0 ≤ z := predecessorExponent_nonneg J (by omega) X hX n
  have hE : 1 ≤ E := exponential_one_le J (by omega) X c hX (zero_le_one.trans hc) n
  have hF : 1 ≤ F := polynomialFactor_one J (by omega) X hX n
  have hF0 := zero_le_one.trans hF
  have hE0 := zero_le_one.trans hE
  have hFE : 1 ≤ F*E := one_le_mul_of_one_le_of_one_le hF hE
  have hFF : F ≤ F*E := le_mul_of_one_le_right hF0 hE
  have hEE : E ≤ F*E := le_mul_of_one_le_left hE0 hF
  have hExp : exp z ≤ E := exp_le_exp.mpr (by nlinarith only [hz,hc])
  have hKd : K ≤ exp (d*z) := hK.trans (previousFrequency_power_le J D hJ X d hX hd hbaseK n)
  have hKE : K ≤ E := hKd.trans (exp_le_exp.mpr (mul_le_mul_of_nonneg_right hdc hz))
  have hKF : K ≤ F*E := hKE.trans hEE
  have hT := inverse_time_le_factor J (by omega) X hX n
  have hTiF : Ti ≤ 2*(F*E) := hTi.trans (hT.trans (mul_le_mul_of_nonneg_left hFF (by norm_num)))
  have hTiTotalF : TiTotal ≤ 2*(F*E) :=
    hTiTotal.trans (hT.trans (mul_le_mul_of_nonneg_left hFF (by norm_num)))
  have hxn := sequence_initial_le J (by omega) X (zero_le_one.trans hX) n
  have hxpow : X^1000 ≤ F := by
    have hp := monomial_le_polynomialFactor J (by omega) X hX n 0 1000 (by decide) le_rfl
    simp only [pow_zero,one_mul] at hp
    exact (pow_le_pow_left₀ (zero_le_one.trans hX) hxn 1000).trans hp
  have hBF : B ≤ CB*(F*E) := hBc.trans
    (mul_le_mul_of_nonneg_left (hxpow.trans hFF) hB)
  have hξE : ξ ≤ Cξ*E := by
    apply hξ.trans
    apply mul_le_mul_of_nonneg_left _ hξC
    apply (pow_le_pow_left₀ hK0 hKd R).trans
    rw [← exp_nat_mul]
    apply exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_right hRc hz]
  have hξF : ξ ≤ Cξ*(F*E) := hξE.trans (mul_le_mul_of_nonneg_left hEE hξC)
  have hDF : (spike J X n)⁻¹ ≤ F*E :=
    (spike_inverse_le_exponential J hJ X hX n).trans (hExp.trans hEE)
  have hhF : shear J X n ≤ F*E :=
    (shear_le_exponential J hJ X hX n).trans (hExp.trans hEE)
  have hΘbig : Θ ≤ 2*Cθ*((J+n : ℕ) : ℝ)^2*(scaleSequence J X n)^2 :=
    hΘ.trans (sourceTheta_bounds (by omega) hθ
      (fun m => sequence_one_le J (by omega) X hX m) n).2
  have hEibig : Ei ≤ 2*exp z := hEi.trans
    (mul_le_mul_of_nonneg_left (previousShear_le_exponential J hJ X hX hbaseH n) (by norm_num))
  have hsmallpoly : ((J+n : ℕ) : ℝ)^20*(scaleSequence J X n)^20 ≤ F :=
    monomial_le_polynomialFactor J (by omega) X hX n 20 20 le_rfl (by decide)
  have hCpF : Cp ≤ (1120*(2*Cθ)^10)*(F*E) := by
    calc
      _ ≤ 560*(2*Cθ*((J+n : ℕ) : ℝ)^2*(scaleSequence J X n)^2)^10*(2*exp z) := by
        apply hCp.trans
        gcongr
      _ = (1120*(2*Cθ)^10)*(((J+n : ℕ) : ℝ)^20*(scaleSequence J X n)^20)*exp z := by
        simp only [mul_pow,← pow_mul]
        ring
      _ ≤ (1120*(2*Cθ)^10)*F*E := by
        gcongr
      _ = _ := by ring
  have hsum : parameterSize K Ti TiTotal Cp B (spike J X n) ξ+shear J X n ≤
      boundConstant Cθ CB Cξ*(F*E) := by
    unfold parameterSize boundConstant
    nlinarith only [hFE,hKF,hTiF,hTiTotalF,hBF,hξF,hDF,hhF,hCpF]
  apply hsum.trans_eq
  dsimp [F,E,z,parameterEnvelope,polynomialFactor,predecessorExponent]
  ring

end EulerPacketParameterEnvelope

end
end

end

section

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

end
end

end

@[expose] public section

noncomputable section

namespace EulerNormalPacketParameters

open Real EulerPacketLowConstants EulerParentPacketParameterCaps
  EulerPacketUniformFrequencyScales EulerPacketUniformSource EulerPacketSourceFrequency
  EulerPacketSourceScaleChoice EulerPacketSourceScaleSequence EulerPacketSourceParameterScales

/-- Terminal cap, given by `1+terminalConstant gradientConstant hessianConstant`. -/
def terminalCap : ℝ := 1+terminalConstant gradientConstant hessianConstant
/-- Source constant, given by `EulerPacketParameterEnvelope.boundConstant C (boundaryConstant
gradientConstant) terminalCap`. -/
def sourceConstant (C : ℝ) : ℝ :=
  EulerPacketParameterEnvelope.boundConstant C (boundaryConstant gradientConstant) terminalCap

theorem terminalCap_one : 1 ≤ terminalCap := by
  have h := terminalConstant_nonneg gradientConstant hessianConstant hessian_nonneg
  unfold terminalCap
  linarith only [h]

theorem sourceConstant_pos (C : ℝ) : 0 < sourceConstant C :=
  EulerPacketParameterEnvelope.constant_pos C (boundaryConstant gradientConstant) terminalCap
    (boundaryConstant_pos gradientConstant gradient_nonneg).le (zero_le_one.trans terminalCap_one)

/-- Envelope, given by `parameterEnvelope J (sourceConstant C) 320 20 1000 X n`. -/
def envelope (J : ℕ) (C X : ℝ) (n : ℕ) : ℝ := parameterEnvelope J (sourceConstant C) 320 20 1000 X n

/-- Frequency spec, constructed using `frequencyCostSpec`. -/
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
  (m : Space) (hm : ‖m‖ = 1) (R : U ≃ₗᵢ[ℝ] referencePlane m)
  (support : Set Space) (hsupport : IsCompact support)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < A.T)
  (P : ParentFrame (A.transverseData m hm R support hsupport) τ)
  (G : Guards hτ hτT P (A.historyOn H m hm R support hsupport τ hτ hτT))

theorem normalParameterSize_bound (J D : ℕ) (hJ : 2 ≤ J) (C X : ℝ) (hC : 1 ≤ C) (hX : 1 ≤ X)
    (n : ℕ) (Ti TiTotal : ℝ)
    (hbaseH : X ^ 1000 ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 7))
    (hbaseK : X ^ D ≤ exp (X / ((J - 1 : ℕ) : ℝ) ^ 4))
    (hK : L.K ≤ previousFrequency J D X n ^ 80)
    (hTi : Ti ≤ 12 / baseHorizon J X) (hTiTotal : TiTotal ≤ 12 / baseHorizon J X)
    (hBc : H.Bc ≤ gradientConstant * X ^ 1000 + 2)
    (hL : H.L = EulerMeanHarmonic.boundaryLocalizationC1 * H.Bc + 1)
    (hM : G.CM = gradientConstant) (hH : G.CH = hessianConstant)
    (hΘ : P.horizon ≤ sourceTheta J C (scaleSequence J X) n)
    (hδ : G.δ = spike J X n) (hh : G.hchild = shear J X n)
    (hshear : P.shear = previousShear J X n) :
    L.geometryParameterSize H m hm R support hsupport τ hτ hτT P G Ti TiTotal G.terminal ≤
      envelope J C X n := by
  have hprev : 1 ≤ P.shear := hshear.symm ▸ previousShear_one J (by omega) X hX n
  have hterm := L.selected_terminal_bound m hm R support hsupport G hprev
  rw [hM,hH] at hterm
  have hterm' : ‖G.terminal‖ ≤ terminalCap*L.K^4 := hterm.trans
    (mul_le_mul_of_nonneg_right (by
        unfold terminalCap; linarith) (pow_nonneg (zero_le_one.trans L.K_one) _))
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

/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketRadiusCostPolynomial
public import LeanPool.NavierStokesAndEuler.Euler.PacketParentMeanBudget

@[expose] public section

/-! A uniform polynomial bound for the actual initialized common radius.
Primitive scalar bounds are stated explicitly, including the original
source radii; later source constructors discharge them polynomially. -/

noncomputable section

namespace EulerPacketRadiusPolynomial

open Set EulerParameterWordGevrey EulerPacketTerminalDatum EulerTransversePacketProvider
  EulerTransversePacketJoin EulerTransversePacketPrimary EulerTransverseFixedSobolev
  EulerTransverseGevreyInverse EulerTransverseCoefficientGevrey EulerFixedEvolutionSobolev
  EulerTimeLpGramSobolev EulerTimeLpAccelerationSobolev EulerCylinderDirichlet.Coefficients
  EulerSourceCylinderTimeBounds EulerLinearDuhamel EulerPacketCylinderField
    EulerPacketProfileRecursion
  EulerTransverseForwardCoefficientGevrey

attribute [local gcongr] sobolevCoefficientAmplitude_mono_all inverseBlockCost_mono_all
  sobolevInverseCost_mono

theorem coefficientRadius_eq (R : ℝ) : sobolevCoefficientRadius (Fin 4) R=16*R := by
  norm_num [sobolevCoefficientRadius]
  ring

theorem coeff_nonneg (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) : 0 ≤ coeff R C :=
  sobolevCoefficientAmplitude_nonneg 6 R C hR hC

theorem weakEnvelope_nonneg (W : ℝ) (hW : 0 ≤ W) : 0 ≤ weakEnvelope W := by
  have ha := coeff_nonneg W W hW hW
  have hb := coeff_nonneg W (2*W) hW (by positivity)
  exact zero_le_one.trans (inverseBlockCost_one_le 6 (by unfold inverseEnvelope; positivity)
    hW (by unfold formEnvelope; positivity) (by unfold endpointEnvelope; positivity))

theorem strongEnvelope_nonneg (W : ℝ) (hW : 0 ≤ W) : 0 ≤ strongEnvelope W := by
  have ha := coeff_nonneg W W hW hW
  exact zero_le_one.trans (inverseBlockCost_one_le 6 hW hW (by positivity)
    (by unfold endpointEnvelope; positivity))

theorem forwardEnvelope_nonneg (W : ℝ) (hW : 0 ≤ W) : 0 ≤ forwardEnvelope W := by
  have ha := coeff_nonneg (4*W) (1+36*W^4) (by positivity) (by positivity)
  have hi := sobolevInverseCost_nonneg 1 (coeff (4*W) (1+36*W^4)) zero_le_one ha 6
  unfold forwardEnvelope
  positivity

theorem requiredEnvelope_nonneg (W : ℝ) (hW : 0 ≤ W) : 0 ≤ requiredEnvelope W := by
  have hw := weakEnvelope_nonneg W hW
  have hs := strongEnvelope_nonneg W hW
  have hf := forwardEnvelope_nonneg W hW
  unfold requiredEnvelope jetEnvelope
  positivity

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)}
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)

include L in
theorem joined_inverseRadius_nonneg : 0 ≤ L.Ri :=
  (inverseRadius_bounds (D.tail τ hτ.le hτT).frameLower L.C₀ L.Rc L.Ri
    (D.tail τ hτ.le hτT).frameLower_pos L.Rc_nonneg L.forward_inverse).1

variable (W : ℝ) (hW : 1 ≤ W) (hT : D.T ≤ 1)
  (hτi : τ⁻¹ ≤ W)
  (hci : (D.initial τ hτ hτT.le).frameLower⁻¹ ≤ W)
  (hRc : L.Rc ≤ W) (hC0 : L.C₀ ≤ W) (hC1 : L.C₁ ≤ W) (hCH : L.CH ≤ W)
  (hC : L.C ≤ W) (hRi : L.Ri ≤ W) (hR : L.R ≤ W)

include hW hτi hRc hC1 in
theorem endpointForcing_le :
    endpointForcingCost (Fin 4) 6 τ L.Rc L.C₁ ≤ endpointEnvelope W := by
  have hW0 := zero_le_one.trans hW
  have hτ0 := (inv_pos.mpr hτ).le
  have hc := sobolevCoefficientAmplitude_mono_all (ι := Fin 4) 6 L.Rc_nonneg L.C₁_nonneg hRc hC1
  have ha := coeff_nonneg W W hW0 hW0
  unfold endpointForcingCost endpointEnvelope
  gcongr

include hW hτi hci hRc hC0 hC1 hCH in
theorem primary_weak_le : weakRadius L ≤ 2*weakEnvelope W*(16*W+1) := by
  have hW0 := zero_le_one.trans hW
  have ht0 := hτ.le
  have ht1 := L.history_length
  have hc0 := (inv_pos.mpr (D.initial τ hτ hτT.le).frameLower_pos).le
  have h0 := L.C₀_nonneg
  have h1 := L.C₁_nonneg
  have hh := L.CH_nonneg
  have hr := L.Rc_nonneg
  have hInv : inverseCost τ L.C₀ L.C₁ (D.initial τ hτ hτT.le).frameLower ≤ inverseEnvelope W := by
    unfold inverseCost transportCeiling
    calc
      _ ≤ 2*(1+((2*W^2*W^2*W+W*W)*1+W*W))^2 := by gcongr
      _ = _ := by unfold inverseEnvelope; ring
  have hForm : formCost τ L.C₀ L.C₁ L.CH ≤ formEnvelope W := by
    unfold formCost derivativeCost
    calc
      _ ≤ 9*(1*W+W)^2*(1+1^2*W) := by gcongr
      _ = _ := by unfold formEnvelope; ring
  have hEp := endpointForcing_le L W hW hτi hRc hC1
  have he0 : 0 ≤ endpointForcingCost (Fin 4) 6 τ L.Rc L.C₁ := by
    have hb := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) 6 L.Rc L.C₁ hr h1
    unfold endpointForcingCost
    positivity
  have hforce : forcingBlockAmplitude (Fin 4) 6 τ L.Rc L.C₀ L.C₁
      (endpointForcingCost (Fin 4) 6 τ L.Rc L.C₁) ≤ 3*coeff W (2*W)*endpointEnvelope W := by
    have hd : τ*derivativeCost τ L.C₀ L.C₁ ≤ 2*W := by
      unfold derivativeCost
      calc
        _ ≤ 1*(1*W+W) := by gcongr
        _ = _ := by ring
    have hd0 : 0 ≤ τ*derivativeCost τ L.C₀ L.C₁ := by unfold derivativeCost; positivity
    have heW : 0 ≤ endpointEnvelope W := by
      have ha := coeff_nonneg W W hW0 hW0
      unfold endpointEnvelope
      positivity
    have hbW := coeff_nonneg W (2*W) hW0 (by positivity)
    have hb : sobolevCoefficientAmplitude (Fin 4) 6 L.Rc (τ*derivativeCost τ L.C₀ L.C₁) ≤
        coeff W (2*W) := sobolevCoefficientAmplitude_mono_all 6 hr hd0 hRc hd
    unfold forcingBlockAmplitude
    gcongr
  have hi0 : 0 ≤ inverseCost τ L.C₀ L.C₁ (D.initial τ hτ hτT.le).frameLower := by
    unfold inverseCost
    positivity
  have hf0 : 0 ≤ formCost τ L.C₀ L.C₁ L.CH := by unfold formCost derivativeCost; positivity
  have hforce0 := forcingBlockAmplitude_nonneg (Fin 4) 6 τ L.Rc L.C₀ L.C₁
    (endpointForcingCost (Fin 4) 6 τ L.Rc L.C₁) ht0 hr h0 h1 he0
  have hb := inverseBlockCost_mono_all (ι := Fin 4) 6 hi0 hr hf0 hforce0 hInv hRc hForm hforce
  have hw := weakEnvelope_nonneg W hW0
  unfold weakRadius blockCost
  rw [coefficientRadius_eq]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hb (by norm_num)) (by gcongr)
    (by positivity) (by positivity)

include hW hτi hci hRc hC0 hC1 in
theorem primary_gram_le (V : ℝ) (hV : 0 ≤ V) (hVW : V ≤ 2*W+2) :
    gramBlockCost (Fin 4) 6 (D.initial τ hτ hτT.le).frameLower L.Rc L.C₀
      (accelerationBlockAmplitude (Fin 4) 6 L.Rc L.C₀ L.C₁
        (endpointForcingCost (Fin 4) 6 τ L.Rc L.C₁) V) ≤ strongEnvelope W := by
  have hW0 := zero_le_one.trans hW
  have hc0 := (inv_pos.mpr (D.initial τ hτ hτT.le).frameLower_pos).le
  have hr := L.Rc_nonneg
  have h0 := L.C₀_nonneg
  have h1 := L.C₁_nonneg
  have hEp := endpointForcing_le L W hW hτi hRc hC1
  have he0 : 0 ≤ endpointForcingCost (Fin 4) 6 τ L.Rc L.C₁ := by
    have hb := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) 6 L.Rc L.C₁ hr h1
    unfold endpointForcingCost
    positivity
  have hA : accelerationBlockAmplitude (Fin 4) 6 L.Rc L.C₀ L.C₁
      (endpointForcingCost (Fin 4) 6 τ L.Rc L.C₁) V ≤
      3*coeff W W*(endpointEnvelope W+6*coeff W W*(2*W+2)) := by
    have ha0 := coeff_nonneg L.Rc L.C₀ hr h0
    have ha1 := coeff_nonneg L.Rc L.C₁ hr h1
    have haW := coeff_nonneg W W hW0 hW0
    have hb0 : sobolevCoefficientAmplitude (Fin 4) 6 L.Rc L.C₀ ≤ coeff W W :=
      sobolevCoefficientAmplitude_mono_all 6 hr h0 hRc hC0
    have hb1 : sobolevCoefficientAmplitude (Fin 4) 6 L.Rc L.C₁ ≤ coeff W W :=
      sobolevCoefficientAmplitude_mono_all 6 hr h1 hRc hC1
    unfold accelerationBlockAmplitude
    gcongr
  exact inverseBlockCost_mono_all (ι := Fin 4) 6 hc0 hr (by positivity)
    (accelerationBlockAmplitude_nonneg 6 L.Rc L.C₀ L.C₁ _ V hr h0 h1 he0 hV)
    hci hRc (by gcongr) hA

include hW hT hτi hC0 hC1 hC hRi in
theorem primary_forward_le : forwardRadius L ≤ 2*forwardEnvelope W*(64*W+1) := by
  have hW0 := zero_le_one.trans hW
  have hi0 := joined_inverseRadius_nonneg L
  have hc0 := L.C_nonneg
  have h0 := L.C₀_nonneg
  have h1 := L.C₁_nonneg
  have hs0 := (sub_pos.mpr hτT).le
  have hs1 : D.T-τ ≤ 1 := by linarith only [hT,hτ]
  have htrace := EulerPacketParentTransverseCosts.traceCost_le τ W hτ L.history_length hτi
  have htrace0 := traceCost_nonneg τ hτ.le
  have hv : τ⁻¹+traceCost τ ≤ 2*W+2 := by linarith only [hτi,htrace]
  have hv0 : 0 ≤ τ⁻¹+traceCost τ := add_nonneg (inv_nonneg.mpr hτ.le) htrace0
  have hba : frozenAmplitude (D.T-τ) L.C (18*L.Ri*L.C₀*L.C₁) ≤ 1+36*W^4 := by
    unfold frozenAmplitude
    calc
      _ ≤ 1+2*W*1*(18*W*W*W) := by gcongr
      _ = _ := by ring
  have hba0 : 0 ≤ frozenAmplitude (D.T-τ) L.C (18*L.Ri*L.C₀*L.C₁) := by
    unfold frozenAmplitude
    positivity
  have hb : forwardSobolevAmplitude (Fin 4) 6 (D.T-τ) L.C (18*L.Ri*L.C₀*L.C₁) (4*L.Ri) ≤
      coeff (4*W) (1+36*W^4) :=
    sobolevCoefficientAmplitude_mono_all 6 (by positivity) hba0 (by gcongr) hba
  have hb0 : 0 ≤ forwardSobolevAmplitude (Fin 4) 6 (D.T-τ) L.C (18*L.Ri*L.C₀*L.C₁) (4*L.Ri) :=
    sobolevCoefficientAmplitude_nonneg 6 _ _ (by positivity) hba0
  have hbW := coeff_nonneg (4*W) (1+36*W^4) (by positivity) (by positivity)
  have hsi := sobolevInverseCost_mono zero_le_one hb0 le_rfl hb 6
  have hsW := sobolevInverseCost_nonneg 1 (coeff (4*W) (1+36*W^4)) zero_le_one hbW 6
  have hf : forwardSobolevCost (Fin 4) 6 (D.T-τ) L.C (τ⁻¹+traceCost τ)
      (EulerSourceCylinderForwardSobolev.forcingCost (Fin 4) 6 L.Ri L.C₀*0)
      (18*L.Ri*L.C₀*L.C₁) (4*L.Ri) ≤ forwardEnvelope W := by
    unfold forwardSobolevCost forwardEnvelope
    simp only [mul_zero,add_zero]
    exact add_le_add le_rfl (mul_le_mul hsi (add_le_add hb (by gcongr))
      (by positivity) hsW)
  have hfW := forwardEnvelope_nonneg W hW0
  unfold forwardRadius
  rw [coefficientRadius_eq]
  calc
    _ ≤ 2*forwardEnvelope W*(16*(4*W)+1) := by gcongr
    _ = _ := by ring

theorem requiredEnvelope_bounds (W : ℝ) (hW : 0 ≤ W) :
    W ≤ requiredEnvelope W ∧ 16*jetEnvelope W ≤ requiredEnvelope W ∧
    2*weakEnvelope W*(16*W+1) ≤ requiredEnvelope W ∧
    2*strongEnvelope W*(16*W+1) ≤ requiredEnvelope W ∧
    2*forwardEnvelope W*(64*W+1) ≤ requiredEnvelope W := by
  have hw := weakEnvelope_nonneg W hW
  have hs := strongEnvelope_nonneg W hW
  have hf := forwardEnvelope_nonneg W hW
  have hj : 0 ≤ jetEnvelope W := by unfold jetEnvelope; positivity
  have hpw : 0 ≤ weakEnvelope W*(16*W+1) := mul_nonneg hw (by positivity)
  have hps : 0 ≤ strongEnvelope W*(16*W+1) := mul_nonneg hs (by positivity)
  have hpf : 0 ≤ forwardEnvelope W*(64*W+1) := mul_nonneg hf (by positivity)
  unfold requiredEnvelope
  exact ⟨by nlinarith,by nlinarith,by nlinarith,by nlinarith,by nlinarith⟩

theorem jetRadius_le (δ W : ℝ) (hδ : 0 < δ) (hi : δ⁻¹ ≤ W) : jetRadius δ ≤ jetEnvelope W := by
  have hi0 := (inv_pos.mpr hδ).le
  unfold jetRadius jetEnvelope
  rw [← inv_pow]
  gcongr

include hW hT hτi hci hRc hC0 hC1 hCH hC hRi hR in
theorem primary_required_le (δ : ℝ) (hδ : 0 < δ) (hi : δ⁻¹ ≤ W) :
    requiredRadius L (wordRadius (Fin 4) δ) ≤ requiredEnvelope W := by
  have hW0 := zero_le_one.trans hW
  have hb := requiredEnvelope_bounds W hW0
  have hw := primary_weak_le L W hW hτi hci hRc hC0 hC1 hCH
  have hs := primary_gram_le L W hW hτi hci hRc hC0 hC1 1 zero_le_one (by linarith)
  have ht0 := traceCost_nonneg τ hτ.le
  have ht := EulerPacketParentTransverseCosts.traceCost_le τ W hτ L.history_length hτi
  have hu := primary_gram_le L W hW hτi hci hRc hC0 hC1 (traceCost τ) ht0 (by linarith)
  have hf := primary_forward_le L W hW hT hτi hC0 hC1 hC hRi
  have hsw := strongEnvelope_nonneg W hW0
  have hrc0 := L.Rc_nonneg
  have hs' : strongRadius L ≤ 2*strongEnvelope W*(16*W+1) := by
    unfold strongRadius
    rw [coefficientRadius_eq]
    gcongr
  have hu' : uniformRadius L ≤ 2*strongEnvelope W*(16*W+1) := by
    unfold uniformRadius
    rw [coefficientRadius_eq]
    gcongr
  have hd : wordRadius (Fin 4) δ ≤ 16*jetEnvelope W := by
    unfold wordRadius
    rw [coefficientRadius_eq]
    exact mul_le_mul_of_nonneg_left (jetRadius_le δ W hδ hi) (by norm_num)
  unfold requiredRadius
  exact max_le (hd.trans hb.2.1) (max_le (hR.trans hb.1)
    (max_le (hw.trans hb.2.2.1) (max_le (hs'.trans hb.2.2.2.1)
      (max_le (hu'.trans hb.2.2.2.1) (hf.trans hb.2.2.2.2)))))


theorem physicalEnvelope_nonneg (W : ℝ) (hW : 0 ≤ W) : 0 ≤ physicalEnvelope W := by
  have ha := coeff_nonneg (4*W) W (by positivity) hW
  have hb := coeff_nonneg (4*W) (18*W^3) (by positivity) (by positivity)
  have hf := coeff_nonneg (4*W) (3*W^2) (by positivity) (by positivity)
  unfold physicalEnvelope
  positivity

theorem commonEnvelope_nonneg (W : ℝ) (hW : 0 ≤ W) : 0 ≤ commonEnvelope W := by
  have ha := coeff_nonneg W W hW hW
  have hp := physicalEnvelope_nonneg W hW
  unfold commonEnvelope
  positivity

theorem normalEnvelope_nonneg (W : ℝ) (hW : 0 ≤ W) : 0 ≤ normalEnvelope W :=
  coeff_nonneg _ _ (by positivity) (by positivity)

theorem pressureEnvelope_nonneg (W : ℝ) (hW : 0 ≤ W) : 0 ≤ pressureEnvelope W := by
  have ha := coeff_nonneg (4*W) W (by positivity) hW
  have hb := coeff_nonneg (4*W) (3*W^2) (by positivity) (by positivity)
  have hc := commonEnvelope_nonneg W hW
  unfold pressureEnvelope
  positivity

theorem gradeEnvelope_nonneg (W : ℝ) (hW : 0 ≤ W) : 0 ≤ gradeEnvelope W := by
  have hc := commonEnvelope_nonneg W hW
  have hn := normalEnvelope_nonneg W hW
  have hp := pressureEnvelope_nonneg W hW
  have hperiod := (Fact.out : 0 < period).le
  unfold gradeEnvelope
  positivity

theorem meanEnvelope_nonneg (W : ℝ) (hW : 0 ≤ W) : 0 ≤ meanEnvelope W := by
  have ha := coeff_nonneg W W hW hW
  unfold meanEnvelope
  positivity

theorem physicalCost_le (Ri C0 C1 Df Da W : ℝ)
    (hRi0 : 0 ≤ Ri) (hC00 : 0 ≤ C0) (hC10 : 0 ≤ C1)
    (hDf0 : 0 ≤ Df) (hDa0 : 0 ≤ Da) (hW : 0 ≤ W)
    (hRi : Ri ≤ W) (hC0 : C0 ≤ W) (hC1 : C1 ≤ W)
    (hDf : Df ≤ 1) (hDa : Da ≤ 1) :
    physicalCost (Fin 4) 6 Ri C0 C1 Df Da ≤ physicalEnvelope W := by
  have ha0 := coeff_nonneg (4*Ri) C0 (by positivity) hC00
  have ha1 := coeff_nonneg (4*Ri) C1 (by positivity) hC10
  have hab := coeff_nonneg (4*Ri) (18*Ri*C0*C1) (by positivity) (by positivity)
  have haf := coeff_nonneg (4*Ri) (3*Ri*C0) (by positivity) (by positivity)
  have haw := coeff_nonneg (4*W) W (by positivity) hW
  have hbw := coeff_nonneg (4*W) (18*W^3) (by positivity) (by positivity)
  have hfw := coeff_nonneg (4*W) (3*W^2) (by positivity) (by positivity)
  have ha0' : coeff (4*Ri) C0 ≤ coeff (4*W) W :=
    sobolevCoefficientAmplitude_mono_all 6 (by positivity) hC00 (by gcongr) hC0
  have ha1' : coeff (4*Ri) C1 ≤ coeff (4*W) W :=
    sobolevCoefficientAmplitude_mono_all 6 (by positivity) hC10 (by gcongr) hC1
  have hb' : coeff (4*Ri) (18*Ri*C0*C1) ≤ coeff (4*W) (18*W^3) := by
    apply sobolevCoefficientAmplitude_mono_all 6 (by positivity) (by positivity) (by gcongr)
    calc
      _ ≤ 18*W*W*W := by gcongr
      _ = _ := by ring
  have hf' : coeff (4*Ri) (3*Ri*C0) ≤ coeff (4*W) (3*W^2) := by
    apply sobolevCoefficientAmplitude_mono_all 6 (by positivity) (by positivity) (by gcongr)
    calc
      _ ≤ 3*W*W := by gcongr
      _ = _ := by ring
  unfold physicalCost coordinateCost
  calc
    _ ≤ 3*coeff (4*W) W*1+3*coeff (4*W) W*
        (3*coeff (4*W) (18*W^3)*1+3*coeff (4*W) (3*W^2)*1) := by gcongr
    _ = _ := by unfold physicalEnvelope; ring

include hW hτi hRc hC0 hC1 hRi in
theorem joined_common_le : L.commonCost ≤ commonEnvelope W := by
  have hW0 := zero_le_one.trans hW
  have hr := L.Rc_nonneg
  have h0 := L.C₀_nonneg
  have h1 := L.C₁_nonneg
  have hi0 := joined_inverseRadius_nonneg L
  have ht0 := traceCost_nonneg τ hτ.le
  have ht := EulerPacketParentTransverseCosts.traceCost_le τ W hτ L.history_length hτi
  have ht' : traceCost τ ≤ 2*W+2 := by linarith
  have ha0 := coeff_nonneg L.Rc L.C₀ hr h0
  have ha1 := coeff_nonneg L.Rc L.C₁ hr h1
  have haw := coeff_nonneg W W hW0 hW0
  have h0' : coeff L.Rc L.C₀ ≤ coeff W W := sobolevCoefficientAmplitude_mono_all 6 hr h0 hRc hC0
  have h1' : coeff L.Rc L.C₁ ≤ coeff W W := sobolevCoefficientAmplitude_mono_all 6 hr h1 hRc hC1
  have hp := physicalCost_le L.Ri L.C₀ L.C₁ 1 1 W hi0 h0 h1 zero_le_one zero_le_one hW0
    hRi hC0 hC1 le_rfl le_rfl
  unfold EulerTransversePacketJoin.Budget.commonCost EulerTransversePacketJoin.Budget.velocityCost
    EulerTransversePacketJoin.Budget.derivativeCost
  calc
    _ ≤ (3*coeff W W*(2*W+2)+3*coeff W W)+
        (3*coeff W W*(2*W+2)+3*coeff W W+physicalEnvelope W) := by gcongr
    _ = _ := by unfold commonEnvelope; ring

include hW hτi hRc hC0 hC1 hRi in
theorem primary_common_le (H : EulerTransversePacketPrimary.Budget L) :
    H.commonCost ≤ commonEnvelope W := by
  have hW0 := zero_le_one.trans hW
  have hr := L.Rc_nonneg
  have h0 := L.C₀_nonneg
  have h1 := L.C₁_nonneg
  have hi0 := joined_inverseRadius_nonneg L
  have ht0 := traceCost_nonneg τ hτ.le
  have ht := EulerPacketParentTransverseCosts.traceCost_le τ W hτ L.history_length hτi
  have ht' : τ⁻¹+traceCost τ ≤ 2*W+2 := by linarith
  have hcoord0 : 0 ≤ τ⁻¹+traceCost τ := add_nonneg (inv_nonneg.mpr hτ.le) ht0
  have ha0 := coeff_nonneg L.Rc L.C₀ hr h0
  have ha1 := coeff_nonneg L.Rc L.C₁ hr h1
  have haw := coeff_nonneg W W hW0 hW0
  have h0' : coeff L.Rc L.C₀ ≤ coeff W W := sobolevCoefficientAmplitude_mono_all 6 hr h0 hRc hC0
  have h1' : coeff L.Rc L.C₁ ≤ coeff W W := sobolevCoefficientAmplitude_mono_all 6 hr h1 hRc hC1
  have hp := physicalCost_le L.Ri L.C₀ L.C₁ 0 1 W hi0 h0 h1 le_rfl zero_le_one hW0
    hRi hC0 hC1 zero_le_one le_rfl
  change (3*coeff L.Rc L.C₀*(τ⁻¹+traceCost τ)+3*coeff L.Rc L.C₀)+
    (3*coeff L.Rc L.C₁*(τ⁻¹+traceCost τ)+3*coeff L.Rc L.C₀+
      physicalCost (Fin 4) 6 L.Ri L.C₀ L.C₁ 0 1) ≤ _
  calc
    _ ≤ (3*coeff W W*(2*W+2)+3*coeff W W)+
        (3*coeff W W*(2*W+2)+3*coeff W W+physicalEnvelope W) := by gcongr
    _ = _ := by unfold commonEnvelope; ring


omit [CompleteSpace U] in
theorem normal_block_le {qR : ℝ} (N : NormalBudget D 6 qR) (W : ℝ) (hW : 0 ≤ W)
    (hNR : N.Rc ≤ W) (hNC : N.C ≤ W) (hNI : N.Ri ≤ W) :
    N.blockAmplitude ≤ normalEnvelope W := by
  have hr := N.Rc_nonneg
  have hc := N.C_nonneg
  have hi := N.Ri_nonneg
  have hcr : N.coefficientRadius ≤ 5*W+1 := by
    unfold NormalBudget.coefficientRadius Data.correctorCoefficientRadius
    linarith
  have hca : N.coefficientAmplitude ≤ 1+W+6*W^2+729*W^6 := by
    unfold NormalBudget.coefficientAmplitude Data.correctorCoefficientAmplitude
    calc
      _ ≤ 1+W+3*W^2+3*W*W+27*(3*W*W)^2*(3*W^2) := by gcongr
      _ = _ := by ring
  exact sobolevCoefficientAmplitude_mono_all 6 N.coefficient_bounds.1
    N.coefficient_bounds.2.1 hcr hca

theorem pressureCost_le (Ri C Df Dv W : ℝ)
    (hRi0 : 0 ≤ Ri) (hC0 : 0 ≤ C) (hDf0 : 0 ≤ Df) (hDv0 : 0 ≤ Dv)
    (hW : 0 ≤ W) (hRi : Ri ≤ W) (hC : C ≤ W) (hDf : Df ≤ 1)
    (hDv : Dv ≤ commonEnvelope W) :
    EulerSourceNormalResidualBounds.pressureCost (Fin 4) 6 Ri C C Df Dv ≤ pressureEnvelope W := by
  have hc0 := coeff_nonneg (4*Ri) C (by positivity) hC0
  have hf0 := coeff_nonneg (4*Ri) (3*Ri*C) (by positivity) (by positivity)
  have hcW := coeff_nonneg (4*W) W (by positivity) hW
  have hfW := coeff_nonneg (4*W) (3*W^2) (by positivity) (by positivity)
  have hvW := commonEnvelope_nonneg W hW
  have hcb : coeff (4*Ri) C ≤ coeff (4*W) W :=
    sobolevCoefficientAmplitude_mono_all 6 (by positivity) hC0 (by gcongr) hC
  have hfb : coeff (4*Ri) (3*Ri*C) ≤ coeff (4*W) (3*W^2) := by
    apply sobolevCoefficientAmplitude_mono_all 6 (by positivity) (by positivity) (by gcongr)
    calc
      _ ≤ 3*W*W := by gcongr
      _ = _ := by ring
  unfold EulerSourceNormalResidualBounds.pressureCost pressureEnvelope
  gcongr

theorem joined_grade_sum_le (N : NormalBudget D 6 L.R) (W : ℝ) (hW : 0 ≤ W)
    (hNR : N.Rc ≤ W) (hNC : N.C ≤ W) (hNI : N.Ri ≤ W)
    (hcommon : L.commonCost ≤ commonEnvelope W) :
    L.commonCost+L.correctorAmplitude (P := period) N+L.correctorTimeAmplitude (P := period) N+
      3*L.pressureAmplitude (P := period) N ≤ gradeEnvelope W := by
  have hn := normal_block_le N W hW hNR hNC hNI
  have hp := pressureCost_le N.Ri N.C 1 L.commonCost W N.Ri_nonneg N.C_nonneg zero_le_one
    L.commonCost_nonneg hW hNI hNC le_rfl hcommon
  have hN0 := N.blockAmplitude_nonneg
  have hN := normalEnvelope_nonneg W hW
  have hC0 := L.commonCost_nonneg
  have hC := commonEnvelope_nonneg W hW
  have hP := (Fact.out : 0 < period).le
  unfold EulerTransversePacketJoin.Budget.correctorAmplitude
    EulerTransversePacketJoin.Budget.correctorTimeAmplitude
    EulerTransversePacketJoin.Budget.pressureAmplitude
  calc
    _ ≤ commonEnvelope W+27*(normalEnvelope W)^2*(period*commonEnvelope W)+
        108*(normalEnvelope W)^2*(period*commonEnvelope W)+3*(period*pressureEnvelope W) := by
          gcongr
    _ = _ := by unfold gradeEnvelope; ring

theorem primary_grade_sum_le (H : EulerTransversePacketPrimary.Budget L)
    (N : NormalBudget D 6 L.R) (W : ℝ) (hW : 0 ≤ W)
    (hNR : N.Rc ≤ W) (hNC : N.C ≤ W) (hNI : N.Ri ≤ W)
    (hcommon : H.commonCost ≤ commonEnvelope W) :
    H.commonCost+H.correctorAmplitude (P := period) N+H.correctorTimeAmplitude (P := period) N+
      3*H.pressureAmplitude (P := period) N ≤ gradeEnvelope W := by
  have hn := normal_block_le N W hW hNR hNC hNI
  have hp := pressureCost_le N.Ri N.C 0 H.commonCost W N.Ri_nonneg N.C_nonneg le_rfl
    H.commonCost_nonneg hW hNI hNC zero_le_one hcommon
  have hN0 := N.blockAmplitude_nonneg
  have hN := normalEnvelope_nonneg W hW
  have hC0 := H.commonCost_nonneg
  have hC := commonEnvelope_nonneg W hW
  have hP := (Fact.out : 0 < period).le
  unfold EulerTransversePacketPrimary.Budget.correctorAmplitude
    EulerTransversePacketPrimary.Budget.correctorTimeAmplitude
    EulerTransversePacketPrimary.Budget.pressureAmplitude
  calc
    _ ≤ commonEnvelope W+27*(normalEnvelope W)^2*(period*commonEnvelope W)+
        108*(normalEnvelope W)^2*(period*commonEnvelope W)+3*(period*pressureEnvelope W) := by
          gcongr
    _ = _ := by unfold gradeEnvelope; ring

theorem mean_costs_le {M : EulerMeanPacketProvider.Data} {Rm : ℝ}
    (LM : EulerMeanPacketProvider.Budget M 6 Rm) (W : ℝ) (hW : 0 ≤ W)
    (hMT : M.T ≤ 1) (hTi : M.T⁻¹ ≤ W)
    (hRc : LM.Rc ≤ W) (hCF : LM.CF ≤ W) (hCF1 : LM.CF₁ ≤ W) (hCf : LM.Cf ≤ W) :
    LM.velocityCost+LM.derivativeCost+LM.pressureGradientCost ≤ meanEnvelope W := by
  have ht0 := EulerMeanStrongContinuousGevrey.coordinateTraceCost_nonneg M.T M.T_pos.le
  have ht : EulerMeanStrongContinuousGevrey.coordinateTraceCost M.T ≤ W+2 :=
    EulerPacketParentTransverseCosts.traceCost_le M.T W M.T_pos hMT hTi
  have hR0 := LM.coefficient_radius_nonneg
  have hF0 := LM.CF_nonneg
  have hF10 := LM.CF₁_nonneg
  have hf0 := LM.Cf_nonneg
  have ha0 := coeff_nonneg LM.Rc LM.CF hR0 hF0
  have ha1 := coeff_nonneg LM.Rc LM.CF₁ hR0 hF10
  have haW := coeff_nonneg W W hW hW
  have h0b : coeff LM.Rc LM.CF ≤ coeff W W :=
    sobolevCoefficientAmplitude_mono_all 6 hR0 hF0 hRc hCF
  have h1b : coeff LM.Rc LM.CF₁ ≤ coeff W W :=
    sobolevCoefficientAmplitude_mono_all 6 hR0 hF10 hRc hCF1
  change 3*coeff LM.Rc LM.CF*EulerMeanStrongContinuousGevrey.coordinateTraceCost M.T+
    3*(coeff LM.Rc LM.CF₁*EulerMeanStrongContinuousGevrey.coordinateTraceCost M.T+coeff LM.Rc
      LM.CF)+
    3*coeff LM.Rc LM.CF*(LM.Cf+3*coeff LM.Rc LM.CF+
      6*coeff LM.Rc LM.CF₁*EulerMeanStrongContinuousGevrey.coordinateTraceCost M.T) ≤ _
  dsimp only [meanEnvelope]
  gcongr

theorem terminalEnvelope_nonneg (W : ℝ) (hW : 0 ≤ W) : 0 ≤ terminalEnvelope W := by
  have hraw := EulerGevreyCutoff.rawBump_pos_zero
  have hm := terminalMass_nonneg
  have ha := coeff_nonneg (jetEnvelope W) (300*(9/EulerGevreyCutoff.rawBump 0)^3*W^2*terminalMass)
    (by unfold jetEnvelope; positivity) (by positivity)
  unfold terminalEnvelope
  positivity

omit [InnerProductSpace ℝ U] [CompleteSpace U] in
theorem terminal_cost_le (δ W : ℝ) (ξ : U) (hδ : 0 < δ)
    (hi : δ⁻¹ ≤ W) (hξ : ‖ξ‖ ≤ W) :
    wordCost (Fin 4) 6 δ*‖ξ‖ ≤ terminalEnvelope W := by
  have hraw := EulerGevreyCutoff.rawBump_pos_zero
  have hm := terminalMass_nonneg
  have hinv : 0 ≤ δ⁻¹ := (inv_pos.mpr hδ).le
  have hsc : scalarJetCost δ*terminalMass ≤
      300*(9/EulerGevreyCutoff.rawBump 0)^3*W^2*terminalMass := by
    unfold scalarJetCost
    rw [← inv_pow]
    calc
      _ ≤ (3*(9/EulerGevreyCutoff.rawBump 0)^3*(100*W^2))*terminalMass := by gcongr
      _ = _ := by ring
  have hc : wordCost (Fin 4) 6 δ ≤
      coeff (jetEnvelope W) (300*(9/EulerGevreyCutoff.rawBump 0)^3*W^2*terminalMass) :=
    sobolevCoefficientAmplitude_mono_all 6 (jetRadius_nonneg δ)
      (mul_nonneg (scalarJetCost_nonneg δ) hm) (jetRadius_le δ W hδ hi) hsc
  have hc0 := coeff_nonneg (jetEnvelope W) (300*(9/EulerGevreyCutoff.rawBump 0)^3*W^2*terminalMass)
    (by unfold jetEnvelope; positivity) (by positivity)
  exact mul_le_mul hc hξ (norm_nonneg ξ) hc0

end EulerPacketRadiusPolynomial



namespace EulerPacketRadiusPolynomial

open EulerParameterWordGevrey EulerPacketTerminalDatum EulerPacketCylinderField
  EulerPacketProfileRecursion

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : EulerTransversePacketProvider.Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le)}
  {M : EulerMeanPacketProvider.Data} {Rm Tc : ℝ} {O : Operators}
  {C : CoefficientData period Tc O}
  (LM : EulerMeanPacketProvider.Budget M 6 Rm)
  (L : EulerTransversePacketJoin.Budget D τ hτ hτT B (Fin 4) 6)
  (NB : EulerTransversePacketJoin.NormalBudget D 6 L.R)
  (BC : CoefficientBudget C) (δ : ℝ) (ξ : U)

/-- Scalar leaves of the actual source budgets. The original source
radii are included; the new canonical radius is not an input. -/
structure RadiusPrimitives (W : ℝ) : Prop where
  one : 1 ≤ W
  total_time : D.T ≤ 1
  mean_time : M.T ≤ 1
  history_inverse_time : τ⁻¹ ≤ W
  mean_inverse_time : M.T⁻¹ ≤ W
  history_gram : (D.initial τ hτ hτT.le).frameLower⁻¹ ≤ W
  original_joined : L.R ≤ W
  original_mean : Rm ≤ W
  joined_radius : L.Rc ≤ W
  joined_frame : L.C₀ ≤ W
  joined_first : L.C₁ ≤ W
  joined_curvature : L.CH ≤ W
  joined_propagator : L.C ≤ W
  joined_inverse : L.Ri ≤ W
  normal_radius : NB.Rc ≤ W
  normal_amplitude : NB.C ≤ W
  normal_inverse : NB.Ri ≤ W
  mean_radius : LM.Rc ≤ W
  mean_frame : LM.CF ≤ W
  mean_first : LM.CF₁ ≤ W
  mean_forcing : LM.Cf ≤ W
  coefficient_radius : BC.Rc ≤ W
  coefficient_cost : BC.termCost ≤ W
  delta_inverse : δ⁻¹ ≤ W
  terminal : ‖ξ‖ ≤ W

theorem initializedRadius_le_envelope (W : ℝ) (hδ : 0 < δ)
    (H : RadiusPrimitives LM L NB BC δ ξ W) :
    initializedRadius LM L NB BC δ ξ ≤ radiusEnvelope W := by
  have hW0 := zero_le_one.trans H.one
  let Lp := primaryRadiusBudget L δ
  let Np := primaryRadiusNormal L NB δ
  let Hp := primaryRadiusPrimary L δ
  have hLp : Lp.R ≤ requiredEnvelope W :=
    primary_required_le L W H.one H.total_time H.history_inverse_time H.history_gram
      H.joined_radius H.joined_frame H.joined_first H.joined_curvature
      H.joined_propagator H.joined_inverse H.original_joined δ hδ H.delta_inverse
  have hLC : Lp.commonCost ≤ commonEnvelope W :=
    joined_common_le Lp W H.one H.history_inverse_time H.joined_radius H.joined_frame
      H.joined_first H.joined_inverse
  have hHC : Hp.commonCost ≤ commonEnvelope W :=
    primary_common_le Lp W H.one H.history_inverse_time H.joined_radius H.joined_frame
      H.joined_first H.joined_inverse Hp
  have hLS := joined_grade_sum_le Lp Np W hW0 H.normal_radius H.normal_amplitude H.normal_inverse
    hLC
  have hHS := primary_grade_sum_le Lp Hp Np W hW0 H.normal_radius H.normal_amplitude
    H.normal_inverse hHC
  have hMS := mean_costs_le LM W hW0 H.mean_time H.mean_inverse_time H.mean_radius H.mean_frame
    H.mean_first H.mean_forcing
  have hTC := terminal_cost_le δ W ξ hδ H.delta_inverse H.terminal
  have hTC0 : 0 ≤ wordCost (Fin 4) 6 δ*‖ξ‖ := mul_nonneg (wordCost_nonneg 6 δ) (norm_nonneg ξ)
  have hreq0 := requiredEnvelope_nonneg W hW0
  have hmean0 := meanEnvelope_nonneg W hW0
  have hgrade0 := gradeEnvelope_nonneg W hW0
  have hterminal0 := terminalEnvelope_nonneg W hW0
  have hcommon : EulerPacketCommonRadius.commonRadius LM Lp Np BC ≤
      18*W+requiredEnvelope W+meanEnvelope W+gradeEnvelope W := by
    unfold EulerPacketCommonRadius.commonRadius
    rw [coefficientRadius_eq]
    linarith only [hLp,hLS,hMS,H.original_mean,H.coefficient_cost,H.coefficient_radius]
  have h0 := Hp.commonCost_nonneg
  have h1 := Hp.correctorAmplitude_nonneg (P := period) Np
  have h2 := Hp.correctorTimeAmplitude_nonneg (P := period) Np
  have h3 := Hp.pressureAmplitude_nonneg (P := period) Np
  have hb0 : Hp.commonCost ≤ gradeEnvelope W := by linarith only [hHS,h1,h2,h3]
  have hb1 : Hp.correctorAmplitude (P := period) Np ≤ gradeEnvelope W := by linarith only
    [hHS,h0,h2,h3]
  have hb2 : Hp.correctorTimeAmplitude (P := period) Np ≤ gradeEnvelope W := by linarith only
    [hHS,h0,h1,h3]
  have hb3 : 3*Hp.pressureAmplitude (P := period) Np ≤ gradeEnvelope W := by linarith only
    [hHS,h0,h1,h2]
  have hmul {a : ℝ} (ha : a ≤ gradeEnvelope W) :
      a*(wordCost (Fin 4) 6 δ*‖ξ‖) ≤ requiredEnvelope W+gradeEnvelope W*terminalEnvelope W :=
    (mul_le_mul ha hTC hTC0 hgrade0).trans (le_add_of_nonneg_left hreq0)
  have hgrade : Hp.gradeRadius (P := period) Np (wordCost (Fin 4) 6 δ*‖ξ‖) ≤
      requiredEnvelope W+gradeEnvelope W*terminalEnvelope W := by
    unfold EulerTransversePacketPrimary.Budget.gradeRadius
    exact max_le (hLp.trans (le_add_of_nonneg_right (mul_nonneg hgrade0 hterminal0)))
      (max_le (hmul hb0) (max_le (hmul hb1) (max_le (hmul hb2) (hmul hb3))))
  change max (EulerPacketCommonRadius.commonRadius LM Lp Np BC)
    (Hp.gradeRadius (P := period) Np (wordCost (Fin 4) 6 δ*‖ξ‖)) ≤ _
  apply max_le
  · apply hcommon.trans
    unfold radiusEnvelope
    nlinarith only [hreq0,mul_nonneg hgrade0 hterminal0]
  · apply hgrade.trans
    unfold radiusEnvelope
    nlinarith only [hW0,hreq0,hmean0,hgrade0]

theorem initializedRadius_power (W : ℝ) (hδ : 0 < δ)
    (H : RadiusPrimitives LM L NB BC δ ξ W) :
    initializedRadius LM L NB BC δ ξ ≤ radiusConstant*W^radiusPower :=
  (initializedRadius_le_envelope LM L NB BC δ ξ W hδ H).trans (radiusEnvelope_power W H.one)

end EulerPacketRadiusPolynomial
